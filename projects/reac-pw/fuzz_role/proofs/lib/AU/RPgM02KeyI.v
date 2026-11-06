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
   m2k_join and m2k_val ported to image B (fuzz_rate.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02KeyVB.v at f07713e8e823 (its value
   readers m2kb_val) and proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 887bee7c56d (role's Int answer: the value is
   a role when it is 0 or 1) for reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): image B's pcs (KV 0x823d8, FLT
   0x8247c, JN 0x824dc, MAL 0x824f8); the cuts and the shared layer are lib/AU/RPgSeg.v's, lib/AU/RPgM02Base.v's and
   lib/AU/RPgM02KeyBase.v's; the shadow base is s11 (atom 27); the value readers load the flags byte, F and pp from
   the real frame (R+0x40, R+0x38, R+0x140) into s8, s10 and s6 (fuzz_rate: the mask, pp and the code from R+0x148,
   R+0x168, R+0x170), the code is already in s9, and the addresses of the size and the body word are a7 + s7 and
   pp + s7 + [R+0x120], which the engine's alias facts m2ki_alias turn into atom 10 plus a constant; every exit's cut
   is rs_cut_T (fuzz_rate: its A cut), and the join's interface carries role's value tail (the body word as a
   sign-extended word, a role when it is 0 or 1). The join itself is lib/AU/RPgM02KeyV.v. *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes). Proves no function
   (kind: segment lemma): rl_m02_key_val_B : lib/AU/RPgM02KeyBase.v's m2k_val_stmt, KV 0x823d8 -> FLT 0x8247c /
   MAL 0x824f8 / JN 0x824dc, a piece of LLVMFuzzerTestOneInput's segment M02.

   THE CODE (lib/AU/RPgM02Base.v lists it with every pc):
     KV  0x823d8 .. 0x823e8  the type's check 0x823e0 (slow block 0x82834) over a0 = &ent[v], with 0x823e4
                             ld s8,0x40(s1) (the flags byte) in it; 0x823ec lw a1 = type; 0x823f0 li a2,6;
                             0x823f4 ld s10,0x38(s1) (F); 0x823f8 ld s6,0x140(s1) (pp); 0x823fc beq a1,a2 -> FLT;
                             0x82400 li a2,4; 0x82404 bne a1,a2 -> MAL
     Int 0x82408 .. 0x82458  a1 := a7 + s7 = &ent[v] + 4 and its check 0x82414 (slow 0x82930); lw a0 = size;
                             bltu a0,4 -> MAL; s7 := s6 + s7 = &ent[v] - 0x4014; a0 := s7 + [R+0x120] + 4 =
                             &ent[v] + 8 and its check 0x82440 (slow 0x829fc); a0 := s7 + 0x401c; lw a2 = the body
                             word; j JN.
   One entry state at KV: the registers as atoms; the real frame (atom 9) with the cells R+0x38 (F), R+0x40 (the
   flags byte), R+0x120 (0x4018) and R+0x140 (pp); the value entry (atom 10) with its type, size and body word (env
   slots 32 .. 37: the flags byte, F, pp, the type, the size, the body word); the shadow entry m2k_SH; the atom
   facts (closed numerals) and the alias facts m2ki_alias. The three instrumented checks 0x823e0, 0x82414, 0x82440
   pass (the shadow entry: the 16 bytes of ent[v] are marked usable), so their slow blocks return to the fast path
   and the error path is not reached. Section hypotheses: MTL : ameter_laws MT and LAWS : AR_laws rsegs B. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck RPgCheckStr RPgM02Base RPgM02KeyBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the value readers' entry state ===================================== *)
(* the value entry at atom 10: its type, its size and its body word *)
Definition m2ki_ent (t s bw : sv) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 t); YP09.mkChunk 4 (CVal 4 s); YP09.mkChunk 8 (CVal 4 bw)].
(* the real frame at atom 9 with the four cells the readers load: R+0x38 = F (slot 33), R+0x40 = the flags byte
   (slot 32), R+0x120 = 0x4018, R+0x140 = pp (slot 34) *)
Definition m2ki_frame : YP09.region :=
m2_frame 0 0x148 0 0
  [YP09.mkChunk 0x38 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 32 0));
   YP09.mkChunk 0x120 (CVal 8 (SLit 0x4018)); YP09.mkChunk 0x140 (CVal 8 (SOff 34 0))].
(* the alias facts: a7 + s7 = &ent[v] + 4 (0x82408) and pp + s7 = &ent[v] - 0x4014 (0x82428), in the forms the
   engine builds for `add a1,a7,s7` and `add s7,s6,s7` (s6 holds slot 34 after 0x823f8) *)
Definition m2ki_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 17 0) (SOff 23 0), SOff 10 4);
  (SAlu ALU_ADD (SOff 34 0) (SOff 23 0), SOff 10 (-0x4014)) ].
(* atom 9 is s1 = R, atom 27 is s11 = the runtime's shadow offset, atom 10 is a0 = &ent[v], atom 23 is s7 = 104 v
   (v <= 32); every bound a closed numeral *)
Definition m2ki_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0); (23%nat, mkAF 0 3328 0) ] [] m2ki_alias.

Lemma m2ki_facts_ok : forall E R a pp (v : Z),
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 27) = SHADOW_OFF ->
ew E 10 = Z_to_bv 64 a -> ew E 17 = Z_to_bv 64 (pp + 0x4018) -> ew E 23 = Z_to_bv 64 (104 * v) ->
ew E 34 = Z_to_bv 64 pp -> a = pp + 0x4014 + 104 * v -> 0 <= pp -> 0 <= v <= 32 -> 4096 <= a <= 0x7fffff800000 ->
facts_ok E m2ki_facts.
Proof.
intros E R a pp v H9 HR Hal H27 E10 E17 E23 E34 Ha Hpp Hv Hab.
assert (U10 : bv_unsigned (ew E 10) = a) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = 104 * v) by (rewrite E23; apply unsigned_lit_small; lia).
split; [|split; [exact I|]].
- cbn [m2ki_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H9, H27, U10, U23. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  repeat split; try lia.
  all: try apply Z.mod_1_r.
- cbn [m2ki_facts f_alias alias_ok m2ki_alias]. split; [|split; [|exact I]]; apply U_inj.
  + rewrite U_SAlu, (U_atom _ 17 (pp + 0x4018) E17), (U_atom _ 23 (104 * v) E23), (U_atom_off _ 10 a 4 E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
  + rewrite U_SAlu, (U_atom _ 34 pp E34), (U_atom _ 23 (104 * v) E23), (U_atom_off _ 10 a (-0x4014) E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* the state at an exit of a run: the kept-register lists [2; 3; 4], m2k_L5 and L, and the pc *)
Ltac m2ki_exit pc L :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
  pose proof (cs_eq_of_st_ok _ _ ss ms _ _ L HS HAE ltac:(vm_compute; reflexivity)) as CX;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with pc by (vm_compute; reflexivity)
end.
Ltac m2ki_in := cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

(* ===================================== the piece ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ---- KV -> FLT / MAL / JN: 0x823d8 .. 0x823e8 the type's check (decided by the shadow entry over
   [&ent[v], &ent[v] + 16)) with 0x823e4 ld s8 (the flags byte); 0x823ec lw a1 = type; 0x823f0 li a2,6;
   0x823f4 ld s10 (F); 0x823f8 ld s6 (pp); 0x823fc beq a1,a2 -> FLT; 0x82400 li a2,4; 0x82404 bne a1,a2 -> MAL;
   Int: 0x82408 .. 0x82418 the size's check at a7 + s7, 0x8241c lw a0 = size, 0x82424 bltu a0,4 -> MAL;
   0x82428 s7 := s6 + s7; 0x8242c .. 0x82444 the body's check at s7 + [R+0x120] + 4, 0x82448 .. 0x82454 lw a2 = the
   body word at s7 + 0x401c, 0x82458 j JN. No store. ---- *)
Lemma rl_m02_key_val_B : m2k_val_stmt B MT.
Proof using MTL LAWS.
unfold m2k_val_stmt, m2k_K_val.
intros cx POST rec Hpre HMAL HFLT HJN fx3 ly3 S3 W3 regs3 mem3 md3 e v Hbase Hro Hat Hv32 Hent Hm.
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2k_apart B LAWS cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & Hc & _).
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
pose proof (m2k_bw_range e Hewf) as Hbr.
assert (HatA : rs_at_cx rsegs cx W3 mem3 regs3 (rs_L_chk rsegs cx ++ m2k_L_FP cx)).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_forall in Hat |- *. intros f Hf. apply Hat.
  unfold m2k_L_val. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf|Hf]; [left; exact Hf|].
  right. apply in_or_app. right. apply in_or_app. left. exact Hf. }
unfold rs_at_cx, rs_at, rs_L_chk, m2k_L_val, m2k_L_FP in Hat.
rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((A8 & A9 & A19 & A27 & A18 & A20 & AC20 & AC40 & _) &
                 (A10 & A17 & A23 & A25 & _) & (AC38 & AC140 & _) & (AC120 & _)).
cbn [rl_at rl_xv fst snd] in A9, A27, A10, A17, A23, A25, AC40, AC38, AC140, AC120.
set (ea := m2k_ea cx v) in *.
assert (Hea : ea = e_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v) by reflexivity.
assert (Hv32' : 0 <= Z.of_nat v <= 32) by lia.
rewrite (Z.mod_small (e_pp (x_e rsegs cx)) (2 ^ 64)) in AC140 by lia.
rewrite (Z.mod_small (e_F (x_e rsegs cx)) (2 ^ 64)) in AC38 by lia.
rewrite (Z.mod_small 0x4018 (2 ^ 64)) in AC120 by lia.
set (vL := e_fl (x_e rsegs cx) mod 2 ^ 64).
assert (HvL : 0 <= vL < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (extra := [Z_to_bv 64 vL; Z_to_bv 64 (e_F (x_e rsegs cx)); Z_to_bv 64 (e_pp (x_e rsegs cx));
               Z_to_bv 64 (e_type e); Z_to_bv 64 (e_size e); Z_to_bv 64 (m2k_bw e)] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = e_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs3 extra 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs3 9%bv = w64 (e_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E27 : bv_unsigned (ew (Ereg regs3 extra) 27) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs3 extra 27 (27%bv : bv 5) eq_refl).
  assert (G : getr regs3 27%bv = w64 SHADOW_OFF) by exact A27.
  rewrite G. unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 ea)
by (rewrite (ew_Ereg_nat regs3 extra 10 (10%bv : bv 5) eq_refl); exact A10).
assert (E17 : ew (Ereg regs3 extra) 17 = Z_to_bv 64 (e_pp (x_e rsegs cx) + 0x4018))
by (rewrite (ew_Ereg_nat regs3 extra 17 (17%bv : bv 5) eq_refl); exact A17).
assert (E23 : ew (Ereg regs3 extra) 23 = Z_to_bv 64 (104 * Z.of_nat v))
by (rewrite (ew_Ereg_nat regs3 extra 23 (23%bv : bv 5) eq_refl); exact A23).
assert (E34 : ew (Ereg regs3 extra) 34 = Z_to_bv 64 (e_pp (x_e rsegs cx)))
by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U10 : bv_unsigned (ew (Ereg regs3 extra) 10) = ea) by (rewrite E10; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs3 extra) (SOff 32 0) = Z_to_bv 64 vL)
by (apply (m2k_den_extra regs3 extra 0 vL); [reflexivity | lia]).
assert (D33 : sv_denot (Ereg regs3 extra) (SOff 33 0) = Z_to_bv 64 (e_F (x_e rsegs cx)))
by (apply (m2k_den_extra regs3 extra 1 (e_F (x_e rsegs cx))); [reflexivity | lia]).
assert (D34 : sv_denot (Ereg regs3 extra) (SOff 34 0) = Z_to_bv 64 (e_pp (x_e rsegs cx)))
by (apply (m2k_den_extra regs3 extra 2 (e_pp (x_e rsegs cx))); [reflexivity | lia]).
assert (D35 : sv_denot (Ereg regs3 extra) (SOff 35 0) = Z_to_bv 64 (e_type e))
by (apply (m2k_den_extra regs3 extra 3 (e_type e)); [reflexivity | lia]).
assert (D36 : sv_denot (Ereg regs3 extra) (SOff 36 0) = Z_to_bv 64 (e_size e))
by (apply (m2k_den_extra regs3 extra 4 (e_size e)); [reflexivity | lia]).
assert (D37 : sv_denot (Ereg regs3 extra) (SOff 37 0) = Z_to_bv 64 (m2k_bw e))
by (apply (m2k_den_extra regs3 extra 5 (m2k_bw e)); [reflexivity | lia]).
pose (rgs := [m2ki_frame; m2ki_ent (SOff 35 0) (SOff 36 0) (SOff 37 0)]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs3 extra) (mrestrict (w_H W3) mem3)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2_frame_ok _ W3 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (chunk_ok_val rsegs _ _ _ 0x38 8 (SOff 33 0) (e_F (x_e rsegs cx)));
      [exact D33 | cbn; lia | cbn; lia | exact AC38].
    + apply (chunk_ok_val rsegs _ _ _ 0x40 8 (SOff 32 0) vL); [exact D32 | cbn; lia | cbn; lia | exact AC40].
    + apply (chunk_ok_val rsegs _ _ _ 0x120 8 (SLit 0x4018) 0x4018); [reflexivity | cbn; lia | cbn; lia | exact AC120].
    + apply (chunk_ok_val rsegs _ _ _ 0x140 8 (SOff 34 0) (e_pp (x_e rsegs cx)));
      [exact D34 | cbn; lia | cbn; lia | exact AC140].
  - apply (rm_ro_region rsegs _ (w_H W3) mem3 10 ea 0 16); [exact U10 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 35 0) (e_type e)); [exact D35 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvt.
    + apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 36 0) (e_size e)); [exact D36 | cbn; lia | cbn; lia | exact Hvs].
    + apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 37 0) (m2k_bw e)); [exact D37 | exact Hbr | cbn; lia | exact Hvb]. }
assert (Hpd : pairwise_disjoint (Ereg regs3 extra) rgs).
{ unfold rgs, m2ki_ent, m2ki_frame, m2_frame.
  repeat split; try exact I.
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, U10. right. lia. }
assert (HG : facts_ok (Ereg regs3 extra) m2ki_facts)
  by (apply (m2ki_facts_ok _ (e_R (x_e rsegs cx)) ea (e_pp (x_e rsegs cx)) (Z.of_nat v) E9 ltac:(lia) HR16 E27
             E10 E17 E23 E34 Hea ltac:(lia) Hv32' ltac:(lia))).
pose proof (m2_entry (fx := fx3) M2_KV [] rgs m2ki_facts W3 regs3 extra mem3 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd HG) as HS.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH E (mrestrict (w_H W3) mem3)).
{ apply (m2k_sh_ok W3 mem3 E ea);
  [ unfold M2_Bx; apply (U_atom E 27 SHADOW_OFF);
    [subst E; apply bv_eq; rewrite E27; symmetry; apply unsigned_lit_small; unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; lia]
  | apply (U_atom E 10 ea); [exact E10 | lia]
  | exact Hra | exact Happ ]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (e_type e))
by (subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (e_size e))
by (subst E; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (m2k_bw e))
by (subst E; change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
(* the four registers T's cut names beyond rs_L_chk, at an exit state *)
assert (Hf24 : forall regsN, getr regsN (Z_to_bv 5 24) = sv_denot E (SOff 32 0) ->
  getr regsN (Z_to_bv 5 24) = w64 (e_fl (x_e rsegs cx))) by (intros regsN G; rewrite G, D32; apply m2_w64_mod).
assert (Hf26 : forall regsN, getr regsN (Z_to_bv 5 26) = sv_denot E (SOff 33 0) ->
  getr regsN (Z_to_bv 5 26) = w64 (e_F (x_e rsegs cx))) by (intros regsN G; rewrite G, D33; reflexivity).
assert (Hf22 : forall regsN, getr regsN (Z_to_bv 5 22) = sv_denot E (SOff 34 0) ->
  getr regsN (Z_to_bv 5 22) = w64 (e_pp (x_e rsegs cx))) by (intros regsN G; rewrite G, D34; reflexivity).
unfold cfg_at. change (w64 M2_KV) with (Z_to_bv 64 M2_KV).
(* 0x823d8 .. 0x823f8, stop at 0x823fc beq a1,a2 with a1 the type *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_eq_U, (m2k_U_sext32 E 35 (e_type e) E35 Htr), U_lit in Hb by lia.
- (* 0x823fc beq taken: the type is 6, the Float arm *)
  assert (Ht6 : e_type e = POD_FLOAT).
  { apply Z.eqb_eq in Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)) in Hb. exact Hb. }
  m2_run_to m2_awr M2K_FLT. ck_keep m2_kwr.
  m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (24%bv : bv 5) G24. m2k_rsv HS (26%bv : bv 5) G26.
  m2ki_exit M2K_FLT constr:(([10; 17; 23; 25]%bv : list (bv 5))).
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  assert (HT : rs_cut_T (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2k_run_T B MT MTL LAWS cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hro
        HatA HJ);
      [ m2_io | exact C234 | exact CL5
      | etransitivity; [exact (CX 25%bv ltac:(m2ki_in))|]; exact A25
      | exact (Hf22 _ G22) | exact (Hf24 _ G24) | exact (Hf26 _ G26)
      | intros a Ha; exact (KE a Ha (fun x => x)) ]);
  apply (HFLT fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT e v HT)
  end.
  + unfold rs_at_cx, rs_at, m2k_L_flt.
    repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd].
    * etransitivity; [exact (CX 10%bv ltac:(m2ki_in))|]. exact A10.
    * etransitivity; [exact (CX 17%bv ltac:(m2ki_in))|]. exact A17.
    * etransitivity; [exact (CX 23%bv ltac:(m2ki_in))|]. exact A23.
    * rewrite (Z.mod_small 0x4018 (2 ^ 64)) by lia.
      eapply (val_mem_kept rsegs); [|exact AC120]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
      apply KE; [lia | intros []].
  + exact Hv32.
  + apply (m2k_ent_facts_kept W3 W3 mem3 _ e ea); [intros a Ha; exact (KE a Ha (fun x => x)) | exact Hent0].
  + exact Ht6.
  + exact Hm0.
- (* not taken: the type is not 6 *)
  assert (Ht6 : e_type e <> 6).
  { intros Hc6. apply Z.eqb_neq in Hb. apply Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)). exact Hc6. }
  m2_run m2_awr. ck_keep m2_kwr.
  m2_branch Hb2.
  all: rewrite branch_ne_U, (m2k_U_sext32 E 35 (e_type e) E35 Htr), U_lit in Hb2 by lia.
  + (* 0x82404 bne taken: the type is neither 4 nor 6, MAL *)
    assert (Ht4 : e_type e <> 4).
    { intros Hc4. apply negb_true_iff in Hb2. apply Z.eqb_neq in Hb2. apply Hb2.
      apply (m2k_sx_eq _ 4 Htr ltac:(lia)). exact Hc4. }
    m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
    m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (24%bv : bv 5) G24. m2k_rsv HS (26%bv : bv 5) G26.
    m2ki_exit M2_MAL constr:(([25]%bv : list (bv 5))).
    assert (Hxv : Role.expect_value e = (None, -1))
    by (apply m2k_expect_none; left; unfold POD_INT, POD_FLOAT; split; assumption).
    lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
    assert (HT : rs_cut_T (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
    by (apply (m2k_run_T B MT MTL LAWS cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hro
          HatA HJ);
        [ m2_io | exact C234 | exact CL5
        | etransitivity; [exact (CX 25%bv ltac:(m2ki_in))|]; exact A25
        | exact (Hf22 _ G22) | exact (Hf24 _ G24) | exact (Hf26 _ G26)
        | intros a Ha; exact (KE a Ha (fun x => x)) ]);
    apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
    apply (m2k_mal_of_T B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HT);
    [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
    end.
  + (* not taken: the type is 4, the Int arm *)
    assert (Ht4 : e_type e = POD_INT).
    { apply negb_false_iff in Hb2. apply Z.eqb_eq in Hb2. apply (m2k_sx_eq _ 4 Htr ltac:(lia)) in Hb2. exact Hb2. }
    m2_run m2_awr. ck_keep m2_kwr.
    m2_branch Hb3.
    all: rewrite branch_ltu_U, (m2k_U_sext32 E 36 (e_size e) E36 ltac:(lia)), U_lit in Hb3 by lia.
    all: rewrite (m2k_sx_id (e_size e)) in Hb3 by lia.
    * (* 0x82424 bltu taken: the size is below 4, MAL *)
      apply Z.ltb_lt in Hb3.
      m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
      m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (24%bv : bv 5) G24. m2k_rsv HS (26%bv : bv 5) G26.
      m2ki_exit M2_MAL constr:(([25]%bv : list (bv 5))).
      assert (Hxv : Role.expect_value e = (None, -1)) by (apply m2k_expect_none; right; exact Hb3).
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HT : rs_cut_T (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2k_run_T B MT MTL LAWS cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hro
            HatA HJ);
          [ m2_io | exact C234 | exact CL5
          | etransitivity; [exact (CX 25%bv ltac:(m2ki_in))|]; exact A25
          | exact (Hf22 _ G22) | exact (Hf24 _ G24) | exact (Hf26 _ G26)
          | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
      apply (m2k_mal_of_T B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HT);
      [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
      end.
    * (* not taken: the size is at least 4; the body word into a2, to JN *)
      apply Z.ltb_ge in Hb3.
      m2_run_to m2_awr M2K_JN. ck_keep m2_kwr.
      m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (24%bv : bv 5) G24. m2k_rsv HS (26%bv : bv 5) G26.
      m2k_rsv HS (12%bv : bv 5) G12.
      m2ki_exit M2K_JN constr:(([25]%bv : list (bv 5))).
      assert (Hxv : Role.expect_value e = Role.flag_rc (Accessors.s32 (Cursor.rd32 (e_body e))))
      by (apply m2k_expect_int; [exact Ht4 | exact Hb3]).
      assert (Hbw : m2k_bw e = Cursor.rd32 (e_body e)) by exact (m2k_bw_rd32 e Hewf Hb3).
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HT : rs_cut_T (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2k_run_T B MT MTL LAWS cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hro
            HatA HJ);
          [ m2_io | exact C234 | exact CL5
          | etransitivity; [exact (CX 25%bv ltac:(m2ki_in))|]; exact A25
          | exact (Hf22 _ G22) | exact (Hf24 _ G24) | exact (Hf26 _ G26)
          | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HJN fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT (m2k_sx (m2k_bw e)) HT)
      end.
      -- etransitivity; [exact G12|].
         rewrite denot_lit_U, (m2k_U_sext32 E 37 (m2k_bw e) E37 Hbr). reflexivity.
      -- exact (m2k_sx_range _ Hbr).
      -- (* a value below 2 is a role: the body word is 0 or 1 *)
         intros Hlt.
         pose proof (proj1 (m2k_sx_small _ Hbr) Hlt) as H01.
         rewrite Hbw in H01.
         assert (Hs32 : Accessors.s32 (Cursor.rd32 (e_body e)) = Cursor.rd32 (e_body e)).
         { pose proof (m2k_s32_small _ (Cursor.rd32_range (e_body e))) as ((_ & S0) & (_ & S1)).
           destruct H01 as [Z0|Z1]; [rewrite (S0 Z0), Z0 | rewrite (S1 Z1), Z1]; reflexivity. }
         rewrite Hs32 in Hxv.
         destruct (m2k_flag_small (Cursor.rd32 (e_body e)) ltac:(lia)) as (Hs1 & w & Hw & Hz).
         split; [rewrite Hsnd, HE0, Hxv; exact Hs1|].
         rewrite Hfst, HE0, Hxv, Hw. cbn [rs_rcell]. rewrite Hz, Hbw. symmetry. apply m2k_sx_id. lia.
      -- (* a value of 2 or more is malformed *)
         intros Hge.
         assert (Hn01 : ~ (Cursor.rd32 (e_body e) = 0 \/ Cursor.rd32 (e_body e) = 1))
         by (intros Hcc; rewrite <- Hbw in Hcc; apply (m2k_sx_small _ Hbr) in Hcc; lia).
         assert (Hbig : Accessors.s32 (Cursor.rd32 (e_body e)) < 0 \/
           2 <= Accessors.s32 (Cursor.rd32 (e_body e))).
         { pose proof (m2k_s32_small _ (Cursor.rd32_range (e_body e))) as ((S0 & _) & (S1 & _)).
           assert (Accessors.s32 (Cursor.rd32 (e_body e)) <> 0) by (intros Hcc; apply Hn01; left; exact (S0 Hcc)).
           assert (Accessors.s32 (Cursor.rd32 (e_body e)) <> 1) by (intros Hcc; apply Hn01; right; exact (S1 Hcc)).
           lia. }
         rewrite (m2k_flag_big _ Hbig) in Hxv.
         split; [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity].
Qed.
End k.
