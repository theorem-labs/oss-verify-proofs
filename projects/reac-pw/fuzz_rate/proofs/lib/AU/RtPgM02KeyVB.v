(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v, RPgM02KeyI.v and RPgM02KeyV.v
   at 595d8c5dd1b5 (the value language of the value entry's address and of a `lw`, the expect_value cases, the
   shadow entry over the value entry, the value dispatch, the Int arm and the value tail),
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304a (the Float arm: the size test, the `flw` and
   pod_nearest) and proofs/reac-pw/fuzz_rate/lib/A/RtPgScanF.v at 22306b8175e6 (the pairs of the scan across a
   key) for reac-pw/fuzz_rate image A: role's pcs become rate's, the shadow base is rate's s2 (atom 18), role's Role
   answers become Rate.expect_value / Rate.rate_of_pairs, role's value tail (a bound test and check_role) becomes
   rate's check_rate on the hz cell, the out cell is R+0x158, the `flw` is stepped by YA0n.SRr_step, and the key
   compare (the spills, the strcmp wrapper, the mismatch exit to O) is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at 48d3cf0d8e40; m2k_jn_walk,
   m2k_join and m2k_val ported to image B (fuzz_rate.asan-ubsan): image B's pcs (KV 0x82c98, FLT 0x82d70, JN
   0x82dd0, MAL 0x82de0, A 0x82dec), the cuts and the shared layer are lib/AU/RtPgSegB.v's, lib/AU/RtPgM02BaseB.v's and
   lib/AU/RtPgM02KitB.v's; the join's code is s10 (image A: s8) and its kept registers are chb_L, s6, s7 and s10; the
   hz cell is at F+0x2a0; the value readers load the mask, pp and the code from the real frame (R+0x148, R+0x168,
   R+0x170) and form the addresses of the size and the body word from a7 + s8 and pp + s8 + [R+0x138], which the
   engine's alias facts m2kv_alias turn into atom 10 plus a constant. *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves
   no function (kind: segment lemma): two pieces of LLVMFuzzerTestOneInput's segment M02, stated in
   lib/AU/RtPgM02KitB.v (nothing here restates a cut or an interface):
     m2kb_join : m2kb_join_stmt   JN 0x82dd0 -> A 0x82dec
     m2kb_val  : m2kb_val_stmt    KV 0x82c98 -> FLT 0x82d70 / MAL 0x82de0 / JN 0x82dd0

   THE CODE (lib/AU/RtPgM02BaseB.v lists it with every pc):
     KV  0x82c98 .. 0x82ca8  the type's check (slow block 0x83314) over a0 = &ent[v], with 0x82ca4 ld s6,0x148(s1)
                             (the mask) in it; 0x82cac lw a1 = type; 0x82cb0 li a2,6; 0x82cb4 ld a4,0x168(s1) (pp);
                             0x82cb8 ld s10,0x170(s1) (the code); 0x82cbc beq a1,a2 -> FLT; 0x82cc0 li a2,4;
                             0x82cc4 bne a1,a2 -> MAL
     Int 0x82cc8 .. 0x82d18  a1 := a7 + s8 = &ent[v] + 4 and its check (slow 0x83410); lw a0 = size; bltu a0,4 -> MAL;
                             s8 := a4 + s8 = &ent[v] - 0x4014; a0 := s8 + [R+0x138] + 4 = &ent[v] + 8 and its check
                             (slow 0x834d4); a0 := s8 + 0x401c; lw a2 = the body word; j JN
     JN  0x82dd0 .. 0x82ddc  lw a1,0(s5) (the hz cell); mv a0,s10 (= 1); jal check_rate 0x83588 (ra 0x82ddc); j A.
   One entry state at KV: the registers as atoms; the real frame (atom 9) with the cells R+0x138 (0x4018), R+0x148
   (the mask), R+0x168 (pp) and R+0x170 (the code); the value entry (atom 10) with its type, size and body word
   (env slots 32 .. 37: the mask, pp, the code, the type, the size, the body word); the shadow entry m2kb_SH; the
   atom facts (closed numerals) and the alias facts m2kv_alias. Section hypotheses: MTL : ameter_laws MT only (the
   frame's laws are the kernel theorem YG0q.AR_laws_ok, check_rate's contract is lib/AU/RtPgCheck.v's
   rt_check_rate_B). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB RtPgM02KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ===================================== the join's kept registers ===================================== *)
(* sp, rsb_L_chk's five (s0, s1, s3, s4, s5), s6 = the mask, s7 = the flags byte and s10 = the code: all
   callee-saved, and neither JN's runs nor check_rate write them *)
Definition m2kv_L : list (bv 5) := [2; 8; 9; 19; 20; 21; 22; 23; 26]%bv.
Lemma m2kv_L_cs : forall r, In r m2kv_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kv_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma m2kv_chb : forall r, In r chb_L -> In r m2kv_L.
Proof. intros r Hr. cbv [chb_L m2kv_L In] in Hr |- *. tauto. Qed.
Ltac m2kv_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [m2kv_L In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

(* ===================================== the value readers' entry state ===================================== *)
(* the value entry at atom 10: its type, its size and its body word *)
Definition m2kv_ent (t s bw : sv) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 t); YP09.mkChunk 4 (CVal 4 s); YP09.mkChunk 8 (CVal 4 bw)].
(* the real frame at atom 9 with the four cells the readers load: R+0x138 = 0x4018, R+0x148 = the mask (slot 32),
   R+0x168 = pp (slot 33), R+0x170 = the code (slot 34) *)
Definition m2kv_frame : YP09.region :=
m2b_frame 0 0x178 0 0
  [YP09.mkChunk 0x138 (CVal 8 (SLit 0x4018)); YP09.mkChunk 0x148 (CVal 8 (SOff 32 0));
   YP09.mkChunk 0x168 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x170 (CVal 8 (SOff 34 0))].
(* the alias facts: a7 + s8 = &ent[v] + 4 (0x82cc8) and pp + s8 = &ent[v] - 0x4014 (0x82ce8), in the forms the
   engine builds for `add a1,a7,s8` and `add s8,a4,s8` (a4 holds slot 33 after 0x82cb4) *)
Definition m2kv_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 17 0) (SOff 24 0), SOff 10 4);
  (SAlu ALU_ADD (SOff 33 0) (SOff 24 0), SOff 10 (-0x4014)) ].
(* atom 9 is s1 = R, atom 20 is s4 = the runtime's shadow offset, atom 10 is a0 = &ent[v], atom 24 is s8 = 104 v
   (v <= 32); every bound a closed numeral *)
Definition m2kv_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0); (24%nat, mkAF 0 3328 0) ] [] m2kv_alias.

Lemma m2kv_facts_ok : forall E R a pp (v : Z),
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 20) = SHADOW_OFF ->
ew E 10 = Z_to_bv 64 a -> ew E 17 = Z_to_bv 64 (pp + 0x4018) -> ew E 24 = Z_to_bv 64 (104 * v) ->
ew E 33 = Z_to_bv 64 pp -> a = pp + 0x4014 + 104 * v -> 0 <= pp -> 0 <= v <= 32 -> 4096 <= a <= 0x7fffff800000 ->
facts_ok E m2kv_facts.
Proof.
intros E R a pp v H9 HR Hal H20 E10 E17 E24 E33 Ha Hpp Hv Hab.
assert (U10 : bv_unsigned (ew E 10) = a) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = 104 * v) by (rewrite E24; apply unsigned_lit_small; lia).
split; [|split; [exact I|]].
- cbn [m2kv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H9, H20, U10, U24. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  repeat split; try lia.
  all: try apply Z.mod_1_r.
- cbn [m2kv_facts f_alias alias_ok m2kv_alias]. split; [|split; [|exact I]]; apply U_inj.
  + rewrite U_SAlu, (U_atom _ 17 (pp + 0x4018) E17), (U_atom _ 24 (104 * v) E24), (U_atom_off _ 10 a 4 E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
  + rewrite U_SAlu, (U_atom _ 33 pp E33), (U_atom _ 24 (104 * v) E24), (U_atom_off _ 10 a (-0x4014) E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* the state at an exit of a run: the kept-register lists L1 and L2 besides [2; 3; 4] and m2kb_L5, and the pc *)
Ltac m2kv_exit pc L :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ m2kb_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ L HS HAE ltac:(vm_compute; reflexivity)) as CX;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with pc by (vm_compute; reflexivity)
end.
Ltac m2kv_in := cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* what reaching the join A means: rsb_core, the registers of m2kv_L as at JN, and every byte outside the callees'
   stack as at JN *)
Definition m2kv_K (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word)
(W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq m2kv_L regs0 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs M2B_A regs3 mem3 md3) POST.

(* ---- JN 0x82dd0 lw a1,0(s5) (the hz cell, z); 0x82dd4 mv a0,s10 (= 1); 0x82dd8 jal check_rate (ra = 0x82ddc),
   a2 already the sign-extended z; then 0x82ddc j A (no region) ---- *)
Lemma m2kv_jn_walk : forall (cx : rsb_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 z,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x2a0) -> getr regs2 (Z_to_bv 5 26) = w64 1 ->
getr regs2 (Z_to_bv 5 12) = w64 (m2kb_sx z) -> 0 <= z < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x2a0) 4 z ->
m2kv_K cx POST regs2 W2 mem2 ->
SRr rsegs W2 (cfg_at rsegs M2KB_JN regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 z Hpre Hcore Hsp H21 H26 H12 Hz Hcell HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 z]) 21) = q_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x2a0)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs2 [Z_to_bv 64 z]) (SOff 32 0) = Z_to_bv 64 z)
by (apply (m2kb_den_extra regs2 _ 0 z); [reflexivity | lia]).
pose proof (m2b_entry M2KB_JN [] [m2b_hzcell (SOff 32 0)] (mkFacts [] [] []) W2 regs2 [Z_to_bv 64 z] mem2
  (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2b_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SOff 32 0) z E21 ltac:(lia) ltac:(lia) D32 Hz Hcell))
  ltac:(cbn; tauto) ltac:(repeat split)).
remember (Ereg regs2 [Z_to_bv 64 z]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 z]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 (m2kb_sx z))
by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl); exact H12).
assert (E26 : ew E 26 = getr regs2 (Z_to_bv 5 26)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 z) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2KB_JN) with (Z_to_bv 64 M2KB_JN).
(* 0x82dd0 .. 0x82dd8, stop at check_rate's entry 0x83588 *)
m2b_run m2b_awr. ck_keep m2b_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
m2kb_rsv HS (11%bv : bv 5) G11.
m2kb_rsv HS (12%bv : bv 5) G12.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82ddc) by exact R1.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2kv_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_RATE by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2b_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_rate_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2b_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E26. exact H26.
  - rewrite G11, G12, !denot_lit_U, (m2kb_U_sext32 E 32 z E32 Hz),
      (U_atom E 12 (m2kb_sx z) E12 (m2kb_sx_range z Hz)).
    reflexivity. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x82ddc *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq m2kv_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres m2kv_L _ _ m2kv_L_cs Hpres3)).
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as HJ3.
pose proof (m2b_entry 0x82ddc [] [] (mkFacts [] [] []) W3 regs3 [] mem3 (Forall_nil _) eq_refl (Forall_nil _)
  ltac:(cbn; tauto) ltac:(repeat split)) as HS.
remember (Ereg regs3 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
change (w64 0x82ddc) with (Z_to_bv 64 0x82ddc).
m2b_run_to m2b_awr M2B_A. ck_keep m2b_kwr.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2kv_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2B_A by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2b_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 _ _ _ Hcore3 ltac:(eassumption));
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (K3 a Ha Hs).
Qed.
End w.

(* ===================================== the pieces ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ---- JN -> A ---- *)
Lemma m2kb_join : m2kb_join_stmt B MT.
Proof using MTL.
unfold m2kb_join_stmt, m2kb_K_join.
intros cx POST rec Hpre HA fx3 ly3 S3 W3 regs3 mem3 md3 HcA Hrc H12.
pose proof (m2b_stack B cx Hpre) as (HR & _).
pose proof HcA as (Hbase & Hat & Hhz).
pose proof Hbase as (Hcore & _).
pose proof Hat as Hat'. unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat'.
rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as (((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                   (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) & (A26 & A22 & A23 & AC60 & AC168 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, A21, A26, A22, A23, AC60, AC168.
assert (Hsp : spZ regs3 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (Hz : 0 <= rsb_hz rsegs cx rec mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (A26' : getr regs3 (Z_to_bv 5 26) = w64 1) by (rewrite <- Hrc; exact A26).
apply (m2kv_jn_walk (fx := fx3) B MT MTL cx POST ly3 S3 W3 regs3 mem3 md3 (rsb_hz rsegs cx rec mod 2 ^ 32)
  Hpre Hcore Hsp A21 A26' H12 Hz Hhz).
intros ly4 S4 W4 regs4 mem4 md4 Hcore4 HL K4.
apply (HA fx3 ly4 S4 W4 regs4 mem4 md4 rec).
apply (chb_cut_A (fx := fx) B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase).
- unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc, m2kb_L_FP. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; assumption.
- exact Hhz.
- exact Hcore4.
- exact (m2kb_cs_sub _ _ _ _ m2kv_chb HL).
- m2kv_get HL (26%bv : bv 5). exact A26.
- m2kv_get HL (22%bv : bv 5). exact A22.
- m2kv_get HL (23%bv : bv 5). exact A23.
- exact K4.
Qed.

(* ---- KV -> FLT / MAL / JN: 0x82c98 .. 0x82ca8 the type's check (decided by the shadow entry over
   [&ent[v], &ent[v] + 16)) with 0x82ca4 ld s6 (the mask); 0x82cac lw a1 = type; 0x82cb0 li a2,6; 0x82cb4 ld a4 (pp);
   0x82cb8 ld s10 (the code); 0x82cbc beq a1,a2 -> FLT; 0x82cc0 li a2,4; 0x82cc4 bne a1,a2 -> MAL; Int: 0x82cc8 ..
   0x82cd8 the size's check at a7 + s8, 0x82cdc lw a0 = size, 0x82ce4 bltu a0,4 -> MAL; 0x82ce8 s8 := a4 + s8;
   0x82cec .. 0x82d04 the body's check at s8 + [R+0x138] + 4, 0x82d08 .. 0x82d14 lw a2 = the body word at
   s8 + 0x401c, 0x82d18 j JN. No store. ---- *)
Lemma m2kb_val : m2kb_val_stmt B MT.
Proof using MTL.
unfold m2kb_val_stmt, m2kb_K_val.
intros cx POST rec Hpre HMAL HFLT HJN fx3 ly3 S3 W3 regs3 mem3 md3 e v Hbase Hhz Hat Hv32 Hent Hm.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2kb_apart B cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc.
pose proof Hbase as (Hcore & Hfxk & _).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hent as Hent0. pose proof Hm as Hm0.
destruct Hent as (Hewf & Hvt & Hvs & Hvb & Hra & Ha0lo & Ha0hi & Happ).
destruct Hm as (HE0 & Hsnd & Hfst).
assert (Htr : 0 <= e_type e < 2 ^ 32) by (destruct Hewf as (H & _); lia).
assert (Hsr : 0 <= e_size e <= 45) by (destruct Hewf as (_ & _ & H); lia).
pose proof (m2kb_bw_range e Hewf) as Hbr.
assert (HatA : rsb_at_cx rsegs cx W3 mem3 regs3 (rsb_L_chk rsegs cx ++ m2kb_L_FP cx)).
{ unfold rsb_at_cx, rsb_at in Hat |- *. rewrite Forall_forall in Hat |- *. intros f Hf. apply Hat.
  unfold m2kb_L_val. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf|Hf]; [left; exact Hf|].
  right. apply in_or_app. right. apply in_or_app. left. exact Hf. }
unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc, m2kb_L_val, m2kb_L_FP in Hat.
rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                  (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) &
                 (A10 & A17 & A24 & A23 & _) & (AC60 & AC168 & _) & (AC170 & AC138 & _)).
cbn [rt_at rt_xv fst snd] in A9, A20, A10, A17, A24, A23, AC148, AC168, AC170, AC138.
set (ea := m2kb_ea cx v) in *.
assert (Hea : ea = q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v) by reflexivity.
assert (Hv32' : 0 <= Z.of_nat v <= 32) by lia.
rewrite (Z.mod_small (q_pp (x_e rsegs cx)) (2 ^ 64)) in AC168 by lia.
rewrite (Z.mod_small 0x4018 (2 ^ 64)) in AC138 by lia.
set (vM := q_mask (x_e rsegs cx) mod 2 ^ 64).
set (vC := snd (rsb_PA rsegs cx rec) mod 2 ^ 64).
assert (HvM : 0 <= vM < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (HvC : 0 <= vC < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (extra := [Z_to_bv 64 vM; Z_to_bv 64 (q_pp (x_e rsegs cx)); Z_to_bv 64 vC; Z_to_bv 64 (e_type e);
               Z_to_bv 64 (e_size e); Z_to_bv 64 (m2kb_bw e)] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs3 extra 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E20 : bv_unsigned (ew (Ereg regs3 extra) 20) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs3 extra 20 (20%bv : bv 5) eq_refl).
  assert (G : getr regs3 20%bv = w64 SHADOW_OFF) by exact A20.
  rewrite G. unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 ea)
by (rewrite (ew_Ereg_nat regs3 extra 10 (10%bv : bv 5) eq_refl); exact A10).
assert (E17 : ew (Ereg regs3 extra) 17 = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4018))
by (rewrite (ew_Ereg_nat regs3 extra 17 (17%bv : bv 5) eq_refl); exact A17).
assert (E24 : ew (Ereg regs3 extra) 24 = Z_to_bv 64 (104 * Z.of_nat v))
by (rewrite (ew_Ereg_nat regs3 extra 24 (24%bv : bv 5) eq_refl); exact A24).
assert (E33 : ew (Ereg regs3 extra) 33 = Z_to_bv 64 (q_pp (x_e rsegs cx)))
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U10 : bv_unsigned (ew (Ereg regs3 extra) 10) = ea) by (rewrite E10; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs3 extra) (SOff 32 0) = Z_to_bv 64 vM)
by (apply (m2kb_den_extra regs3 extra 0 vM); [reflexivity | lia]).
assert (D33 : sv_denot (Ereg regs3 extra) (SOff 33 0) = Z_to_bv 64 (q_pp (x_e rsegs cx)))
by (apply (m2kb_den_extra regs3 extra 1 (q_pp (x_e rsegs cx))); [reflexivity | lia]).
assert (D34 : sv_denot (Ereg regs3 extra) (SOff 34 0) = Z_to_bv 64 vC)
by (apply (m2kb_den_extra regs3 extra 2 vC); [reflexivity | lia]).
assert (D35 : sv_denot (Ereg regs3 extra) (SOff 35 0) = Z_to_bv 64 (e_type e))
by (apply (m2kb_den_extra regs3 extra 3 (e_type e)); [reflexivity | lia]).
assert (D36 : sv_denot (Ereg regs3 extra) (SOff 36 0) = Z_to_bv 64 (e_size e))
by (apply (m2kb_den_extra regs3 extra 4 (e_size e)); [reflexivity | lia]).
assert (D37 : sv_denot (Ereg regs3 extra) (SOff 37 0) = Z_to_bv 64 (m2kb_bw e))
by (apply (m2kb_den_extra regs3 extra 5 (m2kb_bw e)); [reflexivity | lia]).
pose (rgs := [m2kv_frame; m2kv_ent (SOff 35 0) (SOff 36 0) (SOff 37 0)]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs3 extra) (mrestrict (w_H W3) mem3)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2b_frame_ok _ W3 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (chunk_ok_val rsegs _ _ _ 0x138 8 (SLit 0x4018) 0x4018); [reflexivity | cbn; lia | cbn; lia | exact AC138].
    + apply (chunk_ok_val rsegs _ _ _ 0x148 8 (SOff 32 0) vM); [exact D32 | cbn; lia | cbn; lia | exact AC148].
    + apply (chunk_ok_val rsegs _ _ _ 0x168 8 (SOff 33 0) (q_pp (x_e rsegs cx)));
      [exact D33 | cbn; lia | cbn; lia | exact AC168].
    + apply (chunk_ok_val rsegs _ _ _ 0x170 8 (SOff 34 0) vC); [exact D34 | cbn; lia | cbn; lia | exact AC170].
  - apply (rtmb_ro_region rsegs _ (w_H W3) mem3 10 ea 0 16); [exact U10 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 35 0) (e_type e)); [exact D35 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvt.
    + apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 36 0) (e_size e)); [exact D36 | cbn; lia | cbn; lia | exact Hvs].
    + apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 37 0) (m2kb_bw e)); [exact D37 | exact Hbr | cbn; lia | exact Hvb]. }
assert (Hpd : pairwise_disjoint (Ereg regs3 extra) rgs).
{ unfold rgs, m2kv_ent, m2kv_frame, m2b_frame.
  repeat split; try exact I.
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, U10. right. lia. }
assert (HG : facts_ok (Ereg regs3 extra) m2kv_facts)
  by (apply (m2kv_facts_ok _ (q_R (x_e rsegs cx)) ea (q_pp (x_e rsegs cx)) (Z.of_nat v) E9 ltac:(lia) HR16 E20
             E10 E17 E24 E33 Hea ltac:(lia) Hv32' ltac:(lia))).
pose proof (m2b_entry (fx := fx3) M2B_KV [] rgs m2kv_facts W3 regs3 extra mem3 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd HG) as HS.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx m2kb_SH E (mrestrict (w_H W3) mem3)).
{ apply (m2kb_sh_ok W3 mem3 E ea);
  [ unfold M2B_Bx; apply (U_atom E 20 SHADOW_OFF);
    [subst E; apply bv_eq; rewrite E20; symmetry; apply unsigned_lit_small; unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; lia]
  | apply (U_atom E 10 ea); [exact E10 | lia]
  | exact Hra | exact Happ ]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (e_type e))
by (subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (e_size e))
by (subst E; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (m2kb_bw e))
by (subst E; change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Hf22 : forall regsN, getr regsN (Z_to_bv 5 22) = sv_denot E (SOff 32 0) ->
  getr regsN (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx))) by (intros regsN G; rewrite G, D32; apply m2b_w64_mod).
assert (Hf26 : forall regsN, getr regsN (Z_to_bv 5 26) = sv_denot E (SOff 34 0) ->
  getr regsN (Z_to_bv 5 26) = w64 (snd (rsb_PA rsegs cx rec))) by (intros regsN G; rewrite G, D34; apply m2b_w64_mod).
unfold cfg_at. change (w64 M2B_KV) with (Z_to_bv 64 M2B_KV).
(* 0x82c98 .. 0x82cb8, stop at 0x82cbc beq a1,a2 with a1 the type *)
m2b_run m2b_awr. ck_keep m2b_kwr.
m2b_branch Hb.
all: rewrite branch_eq_U, (m2kb_U_sext32 E 35 (e_type e) E35 Htr), U_lit in Hb by lia.
- (* 0x82cbc beq taken: the type is 6, the Float arm *)
  assert (Ht6 : e_type e = POD_FLOAT).
  { apply Z.eqb_eq in Hb. apply (m2kb_sx_eq _ 6 Htr ltac:(lia)) in Hb. exact Hb. }
  m2b_run_to m2b_awr M2KB_FLT. ck_keep m2b_kwr.
  m2kb_rsv HS (22%bv : bv 5) G22. m2kb_rsv HS (26%bv : bv 5) G26. m2kb_rsv HS (14%bv : bv 5) G14.
  m2kv_exit M2KB_FLT constr:(([10; 17; 23; 24]%bv : list (bv 5))).
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  assert (HA : rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2kb_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
      [ m2b_io | exact C234 | exact CL5 | exact (Hf26 _ G26) | exact (Hf22 _ G22)
      | etransitivity; [exact (CX 23%bv ltac:(m2kv_in))|]; exact A23
      | intros a Ha; exact (KE a Ha (fun x => x)) ]);
  apply (HFLT fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT e v HA)
  end.
  + unfold rsb_at_cx, rsb_at, m2kb_L_flt.
    repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
    * etransitivity; [exact (CX 10%bv ltac:(m2kv_in))|]. exact A10.
    * etransitivity; [exact (CX 17%bv ltac:(m2kv_in))|]. exact A17.
    * etransitivity; [exact (CX 24%bv ltac:(m2kv_in))|]. exact A24.
    * etransitivity; [exact G14|]. rewrite D33. reflexivity.
    * rewrite (Z.mod_small 0x4018 (2 ^ 64)) by lia.
      eapply (val_mem_kept rsegs); [|exact AC138]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
      apply KE; [lia | intros []].
  + exact Hv32.
  + apply (m2kb_ent_facts_kept W3 W3 mem3 _ e ea); [intros a Ha; exact (KE a Ha (fun x => x)) | exact Hent0].
  + exact Ht6.
  + exact Hm0.
- (* not taken: the type is not 6 *)
  assert (Ht6 : e_type e <> 6).
  { intros Hc6. apply Z.eqb_neq in Hb. apply Hb. apply (m2kb_sx_eq _ 6 Htr ltac:(lia)). exact Hc6. }
  m2b_run m2b_awr. ck_keep m2b_kwr.
  m2b_branch Hb2.
  all: rewrite branch_ne_U, (m2kb_U_sext32 E 35 (e_type e) E35 Htr), U_lit in Hb2 by lia.
  + (* 0x82cc4 bne taken: the type is neither 4 nor 6, MAL *)
    assert (Ht4 : e_type e <> 4).
    { intros Hc4. apply negb_true_iff in Hb2. apply Z.eqb_neq in Hb2. apply Hb2.
      apply (m2kb_sx_eq _ 4 Htr ltac:(lia)). exact Hc4. }
    m2b_run_to m2b_awr M2B_MAL. ck_keep m2b_kwr.
    m2kb_rsv HS (22%bv : bv 5) G22. m2kb_rsv HS (26%bv : bv 5) G26.
    m2kv_exit M2B_MAL constr:(([23]%bv : list (bv 5))).
    assert (Hxv : Rate.expect_value e = (None, -1))
    by (apply m2kb_expect_none; left; unfold POD_INT, POD_FLOAT; split; assumption).
    lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
    assert (HA : rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
    by (apply (m2kb_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
        [ m2b_io | exact C234 | exact CL5 | exact (Hf26 _ G26) | exact (Hf22 _ G22)
        | etransitivity; [exact (CX 23%bv ltac:(m2kv_in))|]; exact A23
        | intros a Ha; exact (KE a Ha (fun x => x)) ]);
    apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
    apply (m2kb_mal_of_A B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA);
    [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
    end.
  + (* not taken: the type is 4, the Int arm *)
    assert (Ht4 : e_type e = POD_INT).
    { apply negb_false_iff in Hb2. apply Z.eqb_eq in Hb2. apply (m2kb_sx_eq _ 4 Htr ltac:(lia)) in Hb2. exact Hb2. }
    m2b_run m2b_awr. ck_keep m2b_kwr.
    m2b_branch Hb3.
    all: rewrite branch_ltu_U, (m2kb_U_sext32 E 36 (e_size e) E36 ltac:(lia)), U_lit in Hb3 by lia.
    all: rewrite (m2kb_sx_id (e_size e)) in Hb3 by lia.
    * (* 0x82ce4 bltu taken: the size is below 4, MAL *)
      apply Z.ltb_lt in Hb3.
      m2b_run_to m2b_awr M2B_MAL. ck_keep m2b_kwr.
      m2kb_rsv HS (22%bv : bv 5) G22. m2kb_rsv HS (26%bv : bv 5) G26.
      m2kv_exit M2B_MAL constr:(([23]%bv : list (bv 5))).
      assert (Hxv : Rate.expect_value e = (None, -1)) by (apply m2kb_expect_none; right; exact Hb3).
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HA : rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2kb_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
          [ m2b_io | exact C234 | exact CL5 | exact (Hf26 _ G26) | exact (Hf22 _ G22)
          | etransitivity; [exact (CX 23%bv ltac:(m2kv_in))|]; exact A23
          | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
      apply (m2kb_mal_of_A B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA);
      [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
      end.
    * (* not taken: the size is at least 4; the body word into a2, to JN *)
      apply Z.ltb_ge in Hb3.
      m2b_run_to m2b_awr M2KB_JN. ck_keep m2b_kwr.
      m2kb_rsv HS (22%bv : bv 5) G22. m2kb_rsv HS (26%bv : bv 5) G26. m2kb_rsv HS (12%bv : bv 5) G12.
      m2kv_exit M2KB_JN constr:(([23]%bv : list (bv 5))).
      assert (Hxv : Rate.expect_value e = (Some (Accessors.s32 (Cursor.rd32 (e_body e))), 1))
      by (apply m2kb_expect_int; [exact Ht4 | exact Hb3]).
      assert (Hbw : m2kb_bw e = Cursor.rd32 (e_body e)) by exact (m2kb_bw_rd32 e Hewf Hb3).
      assert (Hhzv : rsb_hz rsegs cx rec mod 2 ^ 32 = m2kb_bw e).
      { unfold rsb_hz, Rate.written_or. rewrite Hfst, HE0, Hxv. cbn [fst].
        rewrite Hbw. apply m2kb_s32_mod. apply Cursor.rd32_range. }
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HA : rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2kb_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
          [ m2b_io | exact C234 | exact CL5 | exact (Hf26 _ G26) | exact (Hf22 _ G22)
          | etransitivity; [exact (CX 23%bv ltac:(m2kv_in))|]; exact A23
          | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HJN fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA)
      end.
      -- rewrite Hsnd, HE0, Hxv. reflexivity.
      -- etransitivity; [exact G12|].
         rewrite denot_lit_U, (m2kb_U_sext32 E 37 (m2kb_bw e) E37 Hbr), Hhzv. reflexivity.
Qed.
End k.

Print Assumptions m2kb_join.
Print Assumptions m2kb_val.
