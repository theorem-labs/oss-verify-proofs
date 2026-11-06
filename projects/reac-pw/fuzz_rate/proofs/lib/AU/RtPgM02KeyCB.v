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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at 48d3cf0d8e40 (the key compare:
   the helpers m2kc_* and the lemmas m2kc_key_str, m2kc_tail, m2k_key) for image B (fuzz_rate.asan-ubsan): image B's
   pcs (KM 0x82c40, the call 0x82c64 of the strcmp wrapper 0x421f4, the tail 0x82c68, O 0x82b48, KV 0x82c98); the
   cuts are lib/AU/RtPgSegB.v's (rs_ -> rsb_) and the interfaces lib/AU/RtPgM02KitB.v's (m2k_ -> m2kb_); the cut's
   `addiw s9,a2,1` with its trap `blt` 0x82c44 and the dead `bltz` 0x82c48 are decided by the engine from a closed
   atom bound on a2 (atom 12), where image A decided one dead `blt` from s6; the four spills are a7, t0, t1, t2 to
   R+0x160, R+0x158, R+0x150, R+0x140 (image A: R+0x110 .. R+0x130) and the reloads give back all four of
   rsb_L_scan's caller-saved operands (t0 = ~&ent[0].body and t1 = 104 << 32 included); s9 = m + 2 is carried over
   the call as a callee-saved register and is the scan's a2 at O; the tail's two trap branches 0x82c88 and 0x82c90
   are decided by the engine from closed atom bounds on s6, s8 and s11, and the flags byte is reloaded from R+0x50
   into s7 before KV; &ent[v] is `add a0,s2,s8` (image A's mulhu form is dropped). *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves no
   function (kind: segment lemma): m2kb_key, lib/AU/RtPgM02KitB.v's m2kb_key_stmt, the key compare of
   LLVMFuzzerTestOneInput's segment M02, from the cut KM 0x82c40 to O 0x82b48 (the key is not "reac.cfg.rate": the
   scan goes on at m + 2) or KV 0x82c98 (the key matched; the interface m2kb_K_val at v = m + 1).

   THE CODE (lib/AU/RtPgM02BaseB.v lists it with every pc):
     KM  0x82c40 addiw s9,a2,1 (a2 = m + 1); 0x82c44 blt s9,a2 -> trap; 0x82c48 bltz a2 -> ABS (dead);
         a1 := 0x20fa0; 0x82c54 .. 0x82c60 sd a7 / t0 / t1 / t2 to R+0x160 / R+0x158 / R+0x150 / R+0x140;
         0x82c64 jal the strcmp wrapper 0x421f4 (a0 = &ent[m].body = pp + 0x401c + 104 m), ra = 0x82c68
     0x82c68 li t3,8; the four reloads; mv a2,s9; 0x82c80 bnez a0 -> O (a2 = m + 2)
     0x82c84 li a0,33; 0x82c88 bgeu s6,a0 -> trap (s6 = m + 1); 0x82c8c ld s7,0x50(s1) (the flags byte);
         0x82c90 bltu s11,s8 -> trap (s11 = ~&ent[0], s8 = 104 (m + 1)); 0x82c94 add a0,s2,s8 = &ent[m + 1]
     KV  0x82c98 (the value readers; lib/AU/RtPgM02KitB.v m2kb_K_val).
   The engine decides the three trap branches and the dead `bltz` itself: its facts carry closed numeral bounds on
   a2 (atom 12, [1, 32]) at KM and on s6 (atom 22, [1, 32]), s8 (atom 24, [104, 3328]) and s11 (atom 27,
   [2^63, 2^64 - 1]) at the tail. Only `bnez a0` is split.

   SECTION HYPOTHESES of m2kb_key: MTL : ameter_laws MT and ASTRCMP : forall fy, astrcmp_realizes (fx := fy) rsegs B
   M2B_STRCMP (the strcmp wrapper's contract at every float state, lib/Reusable/AStrcmpDef.v). The frame's laws come
   from the kernel theorem YG0q.AR_laws_ok. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgStrcmp.
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

(* ===================================== helpers of the key compare ===================================== *)
(* the registers neither the run to the call nor the wrapper writes: sp, gp, tp and the callee-saved s-registers
   other than s9, which the cut's `addiw` writes *)
Definition m2kcb_L : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
Lemma m2kcb_L_cs : forall r, In r m2kcb_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kcb_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Ltac m2kcb_in := cbv [m2kcb_L m2kb_L5 In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma m2kcb_L5_sub : forall r, In r m2kb_L5 -> In r m2kcb_L.
Proof. intros r Hr. cbv [m2kb_L5 In] in Hr. repeat (destruct Hr as [<- | Hr]; [m2kcb_in|]). destruct Hr. Qed.

Lemma m2kcb_nth_skipn : forall {A : Type} (l : list A) (n i : nat) (d : A), nth (n + i) l d = nth i (skipn n l) d.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [Nat.add nth skipn]. apply IH.
Qed.

(* the four spill cells R+0x140 .. R+0x148 and R+0x150 .. R+0x168 lie in M02's write set *)
Lemma m2kcb_spill_E2 : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (cx : rsb_scx rsegs) a,
(q_R (x_e rsegs cx) + 0x140 <= a < q_R (x_e rsegs cx) + 0x148) \/
(q_R (x_e rsegs cx) + 0x150 <= a < q_R (x_e rsegs cx) + 0x168) -> rsb_E2 rsegs cx a.
Proof.
intros fx rc cx a H. left. unfold rt_inw. cbn [hi_w2 rate_himg_B].
rewrite !Exists_cons. cbn [rt_xv fst snd]. lia.
Qed.

(* the facts of the run from KM: atom 9 (R) in [2^46, 2^47], 16-aligned; atom 12 (a2 = m + 1) in [1, 32], which
   decides the trap `blt s9,a2` 0x82c44 (s9 = a2 + 1) and the dead `bltz a2` 0x82c48 *)
Definition m2kcb_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (12%nat, mkAF 1 32 0) ] [] [].
Lemma m2kcb_facts_ok : forall E R v, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 12) = v -> 1 <= v <= 32 -> facts_ok E m2kcb_facts.
Proof.
intros E R v H9 HR Hal H12 Hv. split; [|split; [exact I | exact I]].
cbn [m2kcb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H12. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

(* the facts of the run from the tail 0x82c68: atom 9 (R) as at KM; atom 22 (s6 = m + 1) in [1, 32], which decides
   the trap `bgeu s6,a0` 0x82c88 (a0 = 33); atom 24 (s8 = 104 (m + 1)) in [104, 3328] and atom 27
   (s11 = ~&ent[0]) in [2^63, 2^64 - 1], which decide the trap `bltu s11,s8` 0x82c90 *)
Definition m2kcb_tfacts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF 1 32 0); (24%nat, mkAF 104 3328 0);
          (27%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Lemma m2kcb_tfacts_ok : forall E R v w z, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 22) = v -> 1 <= v <= 32 -> bv_unsigned (ew E 24) = w -> 104 <= w <= 3328 ->
bv_unsigned (ew E 27) = z -> 9223372036854775808 <= z <= 18446744073709551615 -> facts_ok E m2kcb_tfacts.
Proof.
intros E R v w z H9 HR Hal H22 Hv H24 Hw H27 Hz. split; [|split; [exact I | exact I]].
cbn [m2kcb_tfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H22, H24, H27. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

(* the 64-bit complement as the `not` instruction leaves it [RtPgStepsB.v rtb_lnot_w64] *)
Lemma m2kcb_lnot_w64 : forall b, 0 <= b < 2 ^ 64 -> w64 (Z.lnot b) = w64 (2 ^ 64 - 1 - b).
Proof.
intros b Hb. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (Z.lnot b) with ((2 ^ 64 - 1 - b) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z_mod_plus_full. reflexivity.
Qed.

(* an atom plus a constant, and the sum of two atoms, as words *)
Lemma m2kcb_denot_off : forall E (n : nat) (v c : Z), ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn Hv Hc Hs. apply bv_eq. rewrite denot_SOff, Hn.
rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma m2kcb_denot_add : forall E (p n : nat) (b i : Z), ew E p = Z_to_bv 64 b -> ew E n = Z_to_bv 64 i ->
0 <= b -> 0 <= i -> b + i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff p 0) (SOff n 0)) = Z_to_bv 64 (b + i).
Proof.
intros E p n b i Hp Hn Hb Hi Hs.
rewrite (denot_lit_U E). apply (f_equal (Z_to_bv 64)).
rewrite U_SAlu, (U_atom E p b Hp ltac:(lia)), (U_atom E n i Hn ltac:(lia)).
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.

Section m2kcb_a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a region of a state, and the value of one of its chunks *)
Lemma m2kcb_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma m2kcb_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* the wrapper's answer as a 64-bit word *)
Lemma m2kcb_res_range : forall c1 c2, -1 <= strcmp_res c1 c2 <= 1.
Proof.
intros c1 c2. unfold strcmp_res.
destruct (Z.eqb c1 c2); [lia|]. destruct (Z.ltb c1 c2); lia.
Qed.
Lemma m2kcb_mod_zero : forall r, -1 <= r <= 1 -> (r mod 2 ^ 64 = 0 <-> r = 0).
Proof.
intros r Hr. split; intros Hz; [|subst; reflexivity].
assert (Hc : r = -1 \/ r = 0 \/ r = 1) by lia.
destruct Hc as [->|[->| ->]]; [vm_compute in Hz; discriminate | reflexivity | vm_compute in Hz; discriminate].
Qed.
End m2kcb_a.

(* ===================================== the key compare ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis ASTRCMP : forall fy : YK11.FPState, astrcmp_realizes (fx := fy) rsegs B M2B_STRCMP.

(* the key ent[m]'s text at &ent[m].body = pp + 0x401c + 104 m, NUL-terminated inside the first block, with the
   wrapper's range premises on its 46 bytes *)
Lemma m2kcb_key_str : forall (cx : rsb_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 (m : nat) kb,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
(m < length (ents rec))%nat -> key_of (nth m (ents rec) m2kb_d) = Some kb ->
cstr_at rsegs W2 mem2 (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) (map (fun b : byte => bv_unsigned b) kb) /\
(length kb < 45)%nat /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46 /\
shadow_hull_vis (aview rsegs (w_H W2) mem2) (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46 /\
amem_range (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 m kb Hpre (Hcore & _ & _ & _ & Hpp & Hwf & _) Hml Hk.
pose proof (m2kb_apart B cx Hpre) as (Hp0 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (m2kb_nent_le rec Hwf) as Hn32.
pose proof (m2kb_ent_wf_nth rec m Hwf Hml) as Hewf.
destruct (m2kb_key_of_some _ _ Hk) as (Hkb & _ & Hs1 & Hnul).
set (e := nth m (ents rec) m2kb_d) in *.
pose proof (m2kb_ent_mem_len e Hewf) as HL.
pose proof Hewf as (Htr & Hbl & Hsz).
assert (Hk0 : (Z.to_nat (e_size e - 1) < length (e_body e))%nat) by lia.
destruct (m2kb_cstr_bytes (e_body e) _ Hk0 Hnul) as (Hcl & Hci & Hcn).
rewrite <- Hkb in Hcl, Hci, Hcn.
assert (B0 : rtmb_bytes rsegs (w_H W2) mem2 (q_pp (x_e rsegs cx)) (Layout.pp_bytes rec)) by exact Hpp.
unfold Layout.pp_bytes in B0.
pose proof (rtmb_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
  (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec) (m2kb_buf_max rec Hwf) Hn32
  (m2kb_bodies_96 rec Hwf) (w_H W2) mem2 (q_pp (x_e rsegs cx)) m B0 Hml) as BE.
change (Model.Ent 0 0 []) with m2kb_d in BE. fold e in BE.
rewrite rtmb_bytes_aview in BE.
set (x := q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m).
assert (Hbyte : forall i, (i < length (e_body e))%nat ->
  aview rsegs (w_H W2) mem2 (x + Z.of_nat i) = Some (bv_unsigned (nth i (e_body e) NUL))).
{ intros i Hi.
  assert (Hlen : (8 + i < length (Layout.ent_mem e))%nat) by lia.
  pose proof (BE (8 + i)%nat Hlen) as Hb.
  replace (q_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + i))
    with (x + Z.of_nat i) in Hb by (unfold x, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
  rewrite Hb. f_equal. f_equal.
  rewrite m2kcb_nth_skipn. unfold Layout.ent_mem.
  assert (E8 : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
    by (intros; reflexivity).
  rewrite E8, app_nth1 by exact Hi. reflexivity. }
assert (HAR : AR rsegs B ly2 S2 W2 mem2 md2) by exact (proj1 (proj1 Hcore)).
assert (Hin : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2)).
{ pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
  destruct Hcore as (_ & _ & _ & Hperm & _).
  apply (Permutation_in _ (Permutation_sym Hperm)). exact Hppin. }
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in Hpc, Happ.
pose proof (rtmb_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp (x_e rsegs cx)) Layout.PP_SIZE x 46 HAR Hin
  ltac:(unfold x; lia) ltac:(rewrite Hreq; unfold x, Layout.PP_SIZE; lia)) as (Hra & Hhv).
split.
{ split; [|split].
  - intros i Hi. rewrite length_map in Hi.
    replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
    rewrite Hbyte by lia. f_equal.
    rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; lia). rewrite map_nth.
    f_equal. apply (proj1 (Hci (Z.to_nat i) ltac:(lia))).
  - rewrite length_map, Hbyte by lia. f_equal. exact Hcn.
  - apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb. destruct Hb as (i & Hi & <-).
    rewrite length_map in Hi.
    rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; lia). rewrite map_nth.
    exact (proj2 (Hci i Hi)). }
split; [lia|].
split; [exact Hra|].
split; [exact (Hhv ltac:(lia))|].
unfold amem_range. rewrite C5. unfold x.
unfold kLowShadowBeg in Happ.
destruct Happ as [Ha|Ha]; [left | right]; unfold kHighMemBeg, kHighMemEnd in *; lia.
Qed.

(* ---- the tail: the fresh state at 0x82c68 after the call (a0 = the wrapper's answer r0, the four spill cells hold
   t2, t1, t0, a7, s9 = m + 2 and the other callee-saved registers as at the cut) -> O or KV ---- *)
Lemma m2kcb_tail : forall (cx : rsb_scx rsegs) POST (at0 m : nat) (fx2 : YK11.FPState) rec kb
ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (r0 : Z),
rsb_pre rsegs B cx ->
rsb_from_O (fx := fx) rsegs B MT cx POST (S (S m)) ->
m2kb_K_val (fx := fx) B MT cx POST rec ->
rsb_cut_KM (fx := fx) rsegs B MT cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ->
cs_eq m2kcb_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 (Z.of_nat m + 2) ->
getr regs3 (Z_to_bv 5 10) = w64 r0 -> -1 <= r0 <= 1 -> (r0 = 0 <-> kb = Rate.RATE_KEY) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x140) 8 (q_pp (x_e rsegs cx) + 0x401c) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x150) 8 (104 * 2 ^ 32) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x158) 8 (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c)) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x160) 8 (q_pp (x_e rsegs cx) + 0x4018) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
SRr rsegs W2 (@cfg_at fx2 rsegs 0x82c68 regs3 mem3 md3) POST.
Proof using MTL.
intros cx POST at0 m fx2 rec kb ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 r0
  Hpre HO HKV HKM Hcore3 HL H25 H10 Hr0 Hres S140 S150 S158 S160 K3.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2kb_apart B cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc. unfold Layout.PP_SIZE in Hpc.
pose proof HKM as (Hbase & Hat & Hhz & Hinv & Hrec & Ham & Hm & Hq & Hk).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (proj1 Hcore3) as HJ3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (m2kb_nent_le rec Hwf) as Hn32.
assert (HmZ : Z.of_nat m <= 30) by lia.
assert (HatL : rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_chk rsegs cx)).
{ unfold rsb_at_cx, rsb_at, rsb_L_scan in Hat |- *. rewrite !Forall_app in Hat. exact (proj1 (proj1 Hat)). }
unfold rsb_at_cx, rsb_at, rsb_L_scan, rsb_L_chk, rsb_Hc in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                   (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) &
                  (AC170 & AC138 & A28 & A26 & A18 & A17 & A7 & A23 & A27 & A5 & A6 & AC60 & AC168 & _)) &
                 (A10 & A12 & A22 & A24 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, AC178, A21, AC10, AC50, AC170, AC138, A28, A26, A18, A17, A7,
  A23, A27, A5, A6, AC60, AC168, A10, A12, A22, A24.
(* the registers of the state after the call, from the cut's through the kept list *)
assert (A9' : getr regs3 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)))
by (etransitivity; [exact (HL 9%bv ltac:(m2kcb_in))|]; exact A9).
assert (A18' : getr regs3 (Z_to_bv 5 18) = w64 (q_pp (x_e rsegs cx) + 0x4014))
by (etransitivity; [exact (HL 18%bv ltac:(m2kcb_in))|]; exact A18).
assert (A22' : getr regs3 (Z_to_bv 5 22) = w64 (Z.of_nat m + 1))
by (etransitivity; [exact (HL 22%bv ltac:(m2kcb_in))|]; exact A22).
assert (A24' : getr regs3 (Z_to_bv 5 24) = w64 (104 * (Z.of_nat m + 1)))
by (etransitivity; [exact (HL 24%bv ltac:(m2kcb_in))|]; exact A24).
assert (A27' : getr regs3 (Z_to_bv 5 27) = w64 (Z.lnot (q_pp (x_e rsegs cx) + 0x4014)))
by (etransitivity; [exact (HL 27%bv ltac:(m2kcb_in))|]; exact A27).
rewrite (m2kcb_lnot_w64 (q_pp (x_e rsegs cx) + 0x4014) ltac:(lia)) in A27'.
(* the flags byte's cell R+0x50, kept over the call *)
assert (S50 : val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x50) 8 (q_fl (x_e rsegs cx) mod 2 ^ 64))
by (apply (m2kb_cell_kept B cx W2 mem2 W2 mem3 0x50); [exact Hpre | lia | lia | lia | exact K3 | exact AC50]).
pose proof (Z.mod_pos_bound (q_fl (x_e rsegs cx)) (2 ^ 64) ltac:(lia)) as Hfl.
set (extra := [Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4018); Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x401c);
               Z_to_bv 64 (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c)); Z_to_bv 64 (104 * 2 ^ 32);
               Z_to_bv 64 (q_fl (x_e rsegs cx) mod 2 ^ 64)] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs3 extra 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9'.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 (r0 mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs3 extra 10 (10%bv : bv 5) eq_refl).
  assert (G : getr regs3 10%bv = w64 r0) by exact H10.
  rewrite G. symmetry. apply m2b_w64_mod. }
assert (E18 : ew (Ereg regs3 extra) 18 = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4014)).
{ rewrite (ew_Ereg_nat regs3 extra 18 (18%bv : bv 5) eq_refl).
  assert (G : getr regs3 18%bv = w64 (q_pp (x_e rsegs cx) + 0x4014)) by exact A18'. exact G. }
assert (E24v : ew (Ereg regs3 extra) 24 = Z_to_bv 64 (104 * (Z.of_nat m + 1))).
{ rewrite (ew_Ereg_nat regs3 extra 24 (24%bv : bv 5) eq_refl).
  assert (G : getr regs3 24%bv = w64 (104 * (Z.of_nat m + 1))) by exact A24'. exact G. }
assert (E22 : bv_unsigned (ew (Ereg regs3 extra) 22) = Z.of_nat m + 1).
{ rewrite (ew_Ereg_nat regs3 extra 22 (22%bv : bv 5) eq_refl).
  assert (G : getr regs3 22%bv = w64 (Z.of_nat m + 1)) by exact A22'.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E24 : bv_unsigned (ew (Ereg regs3 extra) 24) = 104 * (Z.of_nat m + 1)).
{ rewrite E24v. apply unsigned_lit_small. lia. }
assert (E27 : bv_unsigned (ew (Ereg regs3 extra) 27) = 2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x4014)).
{ rewrite (ew_Ereg_nat regs3 extra 27 (27%bv : bv 5) eq_refl).
  assert (G : getr regs3 27%bv = w64 (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x4014))) by exact A27'.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (D25 : sv_denot (Ereg regs3 extra) (SOff 25 0) = w64 (Z.of_nat m + 2))
by (rewrite (ck_atom regs3 extra 25 (25%bv : bv 5) eq_refl); exact H25).
assert (D32 : sv_denot (Ereg regs3 extra) (SOff 32 0) = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4018))
by (apply (m2kb_den_extra regs3 extra 0); [reflexivity | lia]).
assert (D33 : sv_denot (Ereg regs3 extra) (SOff 33 0) = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x401c))
by (apply (m2kb_den_extra regs3 extra 1); [reflexivity | lia]).
assert (D34 : sv_denot (Ereg regs3 extra) (SOff 34 0) = Z_to_bv 64 (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c)))
by (apply (m2kb_den_extra regs3 extra 2); [reflexivity | lia]).
assert (D35 : sv_denot (Ereg regs3 extra) (SOff 35 0) = Z_to_bv 64 (104 * 2 ^ 32))
by (apply (m2kb_den_extra regs3 extra 3); [reflexivity | lia]).
assert (D36 : sv_denot (Ereg regs3 extra) (SOff 36 0) = Z_to_bv 64 (q_fl (x_e rsegs cx) mod 2 ^ 64))
by (apply (m2kb_den_extra regs3 extra 4); [reflexivity | lia]).
assert (Da0 : sv_denot (Ereg regs3 extra) (SAlu ALU_ADD (SOff 18 0) (SOff 24 0))
  = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4014 + 104 * (Z.of_nat m + 1)))
by (apply (m2kcb_denot_add _ 18 24 _ _ E18 E24v); lia).
pose (rgs := [m2b_frame 0x50 0x58 0 0 [YP09.mkChunk 0x50 (CVal 8 (SOff 36 0))];
              m2b_frame 0x140 0x168 0 0 [YP09.mkChunk 0x140 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x150 (CVal 8 (SOff 35 0));
                                         YP09.mkChunk 0x158 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x160 (CVal 8 (SOff 32 0))]]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs3 extra) (mrestrict (w_H W2) mem3)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2b_frame_ok _ W2 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ _ 0x50 8 (SOff 36 0) (q_fl (x_e rsegs cx) mod 2 ^ 64));
    [exact D36 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hfl | cbn; lia | exact S50].
  - apply (m2b_frame_ok _ W2 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ _ 0x140 8 (SOff 33 0) (q_pp (x_e rsegs cx) + 0x401c));
      [exact D33 | cbn; lia | cbn; lia | exact S140].
    + apply (chunk_ok_val rsegs _ _ _ 0x150 8 (SOff 35 0) (104 * 2 ^ 32));
      [exact D35 | cbn; lia | cbn; lia | exact S150].
    + apply (chunk_ok_val rsegs _ _ _ 0x158 8 (SOff 34 0) (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c)));
      [exact D34 | cbn; lia | cbn; lia | exact S158].
    + apply (chunk_ok_val rsegs _ _ _ 0x160 8 (SOff 32 0) (q_pp (x_e rsegs cx) + 0x4018));
      [exact D32 | cbn; lia | cbn; lia | exact S160]. }
assert (Hpd : pairwise_disjoint (Ereg regs3 extra) rgs).
{ unfold rgs, m2b_frame. cbn [pairwise_disjoint all_disjoint].
  split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9. left. lia. }
pose proof (m2b_entry (fx := fx2) 0x82c68 [] rgs m2kcb_tfacts W2 regs3 extra mem3 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd
  (m2kcb_tfacts_ok _ (q_R (x_e rsegs cx)) (Z.of_nat m + 1) (104 * (Z.of_nat m + 1))
     (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x4014)) E9 ltac:(lia) HR16 E22 ltac:(lia) E24 ltac:(lia) E27 ltac:(lia)))
  as HS.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem3 a)
by (intros; reflexivity).
unfold cfg_at. change (w64 0x82c68) with (Z_to_bv 64 0x82c68).
(* 0x82c68 .. 0x82c7c, stop at 0x82c80 bnez a0 *)
m2b_run m2b_awr. ck_keep m2b_kwr.
m2b_branch Hb.
all: rewrite branch_ne_U, (U_atom E 10 (r0 mod 2 ^ 64) E10 ltac:(apply Z.mod_pos_bound; lia)), U_lit in Hb by lia.
- (* taken: a0 <> 0, the key is not "reac.cfg.rate": back to the outer scan at O with a2 = m + 2 *)
  apply negb_true_iff in Hb. apply Z.eqb_neq in Hb.
  assert (Hne : kb <> Rate.RATE_KEY).
  { intros Hkq. apply Hb. apply m2kcb_mod_zero; [exact Hr0 | apply Hres; exact Hkq]. }
  m2b_run_to m2b_awr RSB_O. ck_keep m2b_kwr.
  m2kb_rsv HS (5%bv : bv 5) G5.
  m2kb_rsv HS (6%bv : bv 5) G6.
  m2kb_rsv HS (7%bv : bv 5) G7.
  m2kb_rsv HS (12%bv : bv 5) G12.
  m2kb_rsv HS (17%bv : bv 5) G17.
  m2kb_rsv HS (28%bv : bv 5) G28.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?msn), HAE : env_agree 32 _ ?E,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msn) ?mdT _,
    KE : forall a, _ -> _ -> aview _ _ (ms_mem ?msn) a = _ |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ m2kb_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [18; 23; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as CO;
    rewrite (st_ok_restrict_mkst rsegs H E ss msn HS eq_refl);
    replace (ss_pc ss) with RSB_O by (vm_compute; reflexivity);
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a ->
      aview rsegs (w_H W2) (ms_mem msn) a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha Hz; rewrite (KE a Ha (fun z => z)); exact (K3 a Ha Hz));
    assert (CL5' : cs_eq m2kb_L5 regs2 (ms_regs msn))
    by (apply (cs_eq_trans _ _ regs3); [exact (m2kb_cs_sub _ _ _ _ m2kcb_L5_sub HL) | exact CL5]);
    assert (HcoreN : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT)
    by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT Hcore3 HJ);
        [ intros r Hr; apply C234; cbv [In];
          destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
        | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
        intros a Ha _ _; exact (KE a Ha (fun z => z)));
    destruct (m2kb_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT
      Hpre Hbase Hhz HcoreN Hfxk K) as (HbaseN & HhzN);
    apply (HO fx2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT rec)
  end.
  split; [exact HbaseN|].
  split; [|split; [exact HhzN | split; [|exact Hrec]]].
  + unfold rsb_at_cx, rsb_at, rsb_L_scan. rewrite !Forall_app. split; [split|].
    * eapply (m2kb_chk_kept B cx W2 mem2 regs2); [exact Hpre | exact HatL | exact CL5' | exact K].
    * repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x170); [exact Hpre | lia | lia | lia | exact K | exact AC170].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x138); [exact Hpre | lia | lia | lia | exact K | exact AC138].
      -- exact G28.
      -- etransitivity; [exact (CO 26%bv ltac:(m2kcb_in))|].
         etransitivity; [exact (HL 26%bv ltac:(m2kcb_in))|]. exact A26.
      -- etransitivity; [exact (CO 18%bv ltac:(m2kcb_in))|].
         etransitivity; [exact (HL 18%bv ltac:(m2kcb_in))|]. exact A18.
      -- etransitivity; [exact G17|]. exact D32.
      -- etransitivity; [exact G7|]. exact D33.
      -- etransitivity; [exact (CO 23%bv ltac:(m2kcb_in))|].
         etransitivity; [exact (HL 23%bv ltac:(m2kcb_in))|]. exact A23.
      -- etransitivity; [exact (CO 27%bv ltac:(m2kcb_in))|].
         etransitivity; [exact (HL 27%bv ltac:(m2kcb_in))|]. exact A27.
      -- etransitivity; [exact G5|]. rewrite D34. symmetry. apply m2kcb_lnot_w64. lia.
      -- etransitivity; [exact G6|]. exact D35.
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x60); [exact Hpre | lia | lia | lia | exact K | exact AC60].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x168); [exact Hpre | lia | lia | lia | exact K | exact AC168].
    * repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia.
      etransitivity; [exact G12|]. exact D25.
  + exact (m2kb_inv_mismatch rec at0 m kb Hinv Ham ltac:(lia) Hq Hk Hne).
- (* not taken: a0 = 0, the key is "reac.cfg.rate": the two trap tests, s7 := the flags byte, a0 := &ent[m + 1]
     and KV *)
  apply negb_false_iff in Hb. apply Z.eqb_eq in Hb.
  assert (Heq : kb = Rate.RATE_KEY) by (apply Hres; apply m2kcb_mod_zero; [exact Hr0 | exact Hb]).
  m2b_run_to m2b_awr M2B_KV. ck_keep m2b_kwr.
  m2kb_rsv HS (10%bv : bv 5) G10.
  m2kb_rsv HS (17%bv : bv 5) G17.
  m2kb_rsv HS (23%bv : bv 5) G23.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?msn), HAE : env_agree 32 _ ?E,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msn) ?mdT _,
    KE : forall a, _ -> _ -> aview _ _ (ms_mem ?msn) a = _ |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ m2kb_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C24;
    rewrite (st_ok_restrict_mkst rsegs H E ss msn HS eq_refl);
    replace (ss_pc ss) with M2B_KV by (vm_compute; reflexivity);
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a ->
      aview rsegs (w_H W2) (ms_mem msn) a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha Hz; rewrite (KE a Ha (fun z => z)); exact (K3 a Ha Hz));
    assert (CL5' : cs_eq m2kb_L5 regs2 (ms_regs msn))
    by (apply (cs_eq_trans _ _ regs3); [exact (m2kb_cs_sub _ _ _ _ m2kcb_L5_sub HL) | exact CL5]);
    assert (HcoreN : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT)
    by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT Hcore3 HJ);
        [ intros r Hr; apply C234; cbv [In];
          destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
        | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
        intros a Ha _ _; exact (KE a Ha (fun z => z)));
    destruct (m2kb_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT
      Hpre Hbase Hhz HcoreN Hfxk K) as (HbaseN & HhzN);
    apply (HKV fx2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT (nth (S m) (ents rec) m2kb_d) (S m) HbaseN HhzN)
  end.
  + unfold rsb_at_cx, rsb_at. rewrite Forall_app. split.
    * eapply (m2kb_chk_kept B cx W2 mem2 regs2); [exact Hpre | exact HatL | exact CL5' | exact K].
    * unfold m2kb_L_val, m2kb_L_FP, m2kb_ea. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      -- etransitivity; [exact G10|]. rewrite Da0. unfold w64. f_equal. lia.
      -- etransitivity; [exact G17|]. exact D32.
      -- replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
         etransitivity; [exact (C24 24%bv ltac:(m2kcb_in))|].
         etransitivity; [exact (HL 24%bv ltac:(m2kcb_in))|]. exact A24.
      -- etransitivity; [exact G23|]. rewrite D36. exact (m2b_w64_mod (q_fl (x_e rsegs cx))).
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x60); [exact Hpre | lia | lia | lia | exact K | exact AC60].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x168); [exact Hpre | lia | lia | lia | exact K | exact AC168].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x170); [exact Hpre | lia | lia | lia | exact K | exact AC170].
      -- eapply (m2kb_cell_kept B cx W2 mem2 _ _ 0x138); [exact Hpre | lia | lia | lia | exact K | exact AC138].
  + lia.
  + eapply (m2kb_ent_at (fx := fx) B MT cx fx2 rec ly2 S2 W2); [exact Hpre | exact HbaseN | lia].
  + split; [exact (m2kb_inv_match rec at0 m kb Hinv Ham ltac:(lia) Hq Hk Heq)|].
    destruct Hrec as (_ & _ & _ & Hsnd & Hfst). split; [exact Hsnd | exact Hfst].
Qed.

(* ---- KM 0x82c40: s9 := a2 + 1 = m + 2 and its trap `blt` (not taken), the dead `bltz a2`, a1 := the key literal
   0x20fa0, the four spills, jal the strcmp wrapper 0x421f4 with ra = 0x82c68 ---- *)
Lemma m2kb_key : m2kb_key_stmt B MT.
Proof using MTL ASTRCMP.
unfold m2kb_key_stmt, rsb_from_KM.
intros cx POST inp at0 m Hst HO HKV fx2 ly2 S2 W2 regs2 mem2 md2 rec kb HKM.
pose proof Hst as (Hpre & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2kb_apart B cx Hpre) as (Hp0 & Hpc & Happ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc. unfold Layout.PP_SIZE in Hpc.
pose proof HKM as (Hbase & Hat & Hhz & Hinv & Hrec & Ham & Hm & Hq & Hk).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2kb_nent_le rec Hwf) as Hn32.
assert (HmZ : Z.of_nat m <= 30) by lia.
pose proof (proj1 Hcore) as HJ0.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
clear HJ0.
unfold rsb_at_cx, rsb_at, rsb_L_scan, rsb_L_chk, rsb_Hc in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                   (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) &
                  (AC170 & AC138 & A28 & A26 & A18 & A17 & A7 & A23 & A27 & A5 & A6 & AC60 & AC168 & _)) &
                 (A10 & A12 & A22 & A24 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, AC178, A21, AC10, AC50, AC170, AC138, A28, A26, A18, A17, A7,
  A23, A27, A5, A6, AC60, AC168, A10, A12, A22, A24.
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HspR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
set (x := q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m).
assert (E9 : bv_unsigned (ew (Ereg regs2 []) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 [] 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs2 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E12v : ew (Ereg regs2 []) 12 = Z_to_bv 64 (Z.of_nat m + 1)).
{ rewrite (ew_Ereg_nat regs2 [] 12 (12%bv : bv 5) eq_refl).
  assert (G : getr regs2 12%bv = w64 (Z.of_nat m + 1)) by exact A12. exact G. }
assert (E12 : bv_unsigned (ew (Ereg regs2 []) 12) = Z.of_nat m + 1).
{ rewrite E12v. apply unsigned_lit_small. lia. }
assert (D10 : sv_denot (Ereg regs2 []) (SOff 10 0) = w64 x)
by (rewrite (ck_atom regs2 [] 10 (10%bv : bv 5) eq_refl); exact A10).
assert (D5 : sv_denot (Ereg regs2 []) (SOff 5 0) = w64 (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c))).
{ rewrite (ck_atom regs2 [] 5 (5%bv : bv 5) eq_refl). rewrite <- m2kcb_lnot_w64 by lia. exact A5. }
assert (D6 : sv_denot (Ereg regs2 []) (SOff 6 0) = w64 (104 * 2 ^ 32))
by (rewrite (ck_atom regs2 [] 6 (6%bv : bv 5) eq_refl); exact A6).
assert (D7 : sv_denot (Ereg regs2 []) (SOff 7 0) = w64 (q_pp (x_e rsegs cx) + 0x401c))
by (rewrite (ck_atom regs2 [] 7 (7%bv : bv 5) eq_refl); exact A7).
assert (D17 : sv_denot (Ereg regs2 []) (SOff 17 0) = w64 (q_pp (x_e rsegs cx) + 0x4018))
by (rewrite (ck_atom regs2 [] 17 (17%bv : bv 5) eq_refl); exact A17).
assert (D12 : sv_denot (Ereg regs2 []) (SOff 12 1) = w64 (Z.of_nat m + 2)).
{ rewrite (m2kcb_denot_off _ 12 (Z.of_nat m + 1) 1 E12v ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold w64. f_equal. lia. }
pose (rgs := [m2b_frame 0x140 0x148 0x140 0x148 []; m2b_frame 0x150 0x168 0x150 0x168 []]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs2 []) (mrestrict (w_H W2) mem2)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2b_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia | apply Forall_nil].
  - apply (m2b_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia | apply Forall_nil]. }
assert (Hpd : pairwise_disjoint (Ereg regs2 []) rgs).
{ unfold rgs, m2b_frame. cbn [pairwise_disjoint all_disjoint].
  split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9. left. lia. }
pose proof (m2b_entry (fx := fx2) RSB_KM [] rgs m2kcb_facts W2 regs2 [] mem2 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd
  (m2kcb_facts_ok _ (q_R (x_e rsegs cx)) (Z.of_nat m + 1) E9 ltac:(lia) HR16 E12 ltac:(lia))) as HS.
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((q_R (x_e rsegs cx) + 0x140 <= a < q_R (x_e rsegs cx) + 0x148) \/
     (q_R (x_e rsegs cx) + 0x150 <= a < q_R (x_e rsegs cx) + 0x168)) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 RSB_KM) with (Z_to_bv 64 RSB_KM).
(* 0x82c40 .. 0x82c64, stop at the wrapper's entry 0x421f4 *)
m2b_run m2b_awr. ck_keep m2b_kwr.
m2kb_rsv HS (1%bv : bv 5) G1.
m2kb_rsv HS (10%bv : bv 5) G10.
m2kb_rsv HS (11%bv : bv 5) G11.
m2kb_rsv HS (25%bv : bv 5) G25c.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82c68) by exact G1.
assert (R10' : getr (ms_regs ms) 10 = w64 x) by (etransitivity; [exact G10|]; exact D10).
assert (R11' : getr (ms_regs ms) 11 = w64 M2B_KEY) by exact G11.
assert (R25' : getr (ms_regs ms) (Z_to_bv 5 25) = w64 (Z.of_nat m + 2))
by (etransitivity; [exact G25c|]; exact D12).
(* the four spill cells of the state after the run *)
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  let g0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
  let g1 := eval vm_compute in (nth_error (ss_mem ss) 1) in
  lazymatch g0 with Some ?r0 => lazymatch g1 with Some ?r1 =>
  assert (HR0 : region_ok rsegs E (mrestrict H (ms_mem ms)) r0)
  by (apply (m2kcb_region_nth H E ss ms 0); [exact HS | vm_compute; reflexivity]);
  assert (HR1 : region_ok rsegs E (mrestrict H (ms_mem ms)) r1)
  by (apply (m2kcb_region_nth H E ss ms 1); [exact HS | vm_compute; reflexivity]) end end
end.
assert (E9' : bv_unsigned (ew E 9) = q_R (x_e rsegs cx)) by (subst E; exact E9).
assert (T140 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x140) 8
  (q_pp (x_e rsegs cx) + 0x401c)).
{ pose proof (m2kcb_field E _ 9%nat (q_R (x_e rsegs cx)) _ _ _ _ _ 0x140 8 (SOff 7 0)
    (q_pp (x_e rsegs cx) + 0x401c) HR0 E9' ltac:(cbn; tauto) D7 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T150 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x150) 8 (104 * 2 ^ 32)).
{ pose proof (m2kcb_field E _ 9%nat (q_R (x_e rsegs cx)) _ _ _ _ _ 0x150 8 (SOff 6 0)
    (104 * 2 ^ 32) HR1 E9' ltac:(cbn; tauto) D6 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T158 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x158) 8
  (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c))).
{ pose proof (m2kcb_field E _ 9%nat (q_R (x_e rsegs cx)) _ _ _ _ _ 0x158 8 (SOff 5 0)
    (2 ^ 64 - 1 - (q_pp (x_e rsegs cx) + 0x401c)) HR1 E9' ltac:(cbn; tauto) D5 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T160 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x160) 8
  (q_pp (x_e rsegs cx) + 0x4018)).
{ pose proof (m2kcb_field E _ 9%nat (q_R (x_e rsegs cx)) _ _ _ _ _ 0x160 8 (SOff 17 0)
    (q_pp (x_e rsegs cx) + 0x4018) HR1 E9' ltac:(cbn; tauto) D17 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
(* the registers of the call state, and the kept bytes *)
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2kcb_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2B_STRCMP by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2b_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hz. apply (KE a Ha). intros Hcc. apply Hz. unfold m2kb_wz. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore
      ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2b_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ He; apply (KE a Ha); intros Hcc; exact (He (m2kcb_spill_E2 cx a Hcc)))
end.
destruct (m2kb_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  Hpre Hbase Hhz HcoreT Hfxk KT) as (HbaseT & HhzT).
destruct (m2kcb_key_str cx fx2 rec ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ m kb Hpre HbaseT ltac:(lia) Hk)
  as (Hcx & Hxlen & Hrx46 & Hhx46 & Hmx46).
fold x in Hcx, Hrx46, Hhx46, Hmx46.
assert (HyT : rt_cstr rsegs (w_H W2) (ms_mem ms) M2B_KEY (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY))
  by exact (m2b_key_at B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT).
assert (Hklen : Z.of_nat (length (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY)) = 13)
  by (vm_compute; reflexivity).
assert (Hxl : Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb)) < 45)
  by (rewrite length_map; lia).
destruct (str_meet_of_cstr rsegs (map (fun b : byte => bv_unsigned b) kb) W2 (ms_mem ms) x
  (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY) M2B_KEY Hcx
  (cstr_at_of_rt_cstr rsegs W2 (ms_mem ms) M2B_KEY _ HyT))
as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres0).
assert (Hres : strcmp_res c1 c2 = 0 <-> kb = Rate.RATE_KEY).
{ split; intros H.
  - apply m2kb_map_bv_inj. apply Hres0. exact H.
  - apply Hres0. rewrite H. reflexivity. }
(* the wrapper's premises on the two strings *)
assert (Hx0 : 0 < x) by (unfold x; lia).
assert (Hxhi : x + 46 <= alloc_ceiling) by (unfold x; lia).
destruct (rt_cstr_args rsegs W2 (ms_regs ms) (ms_mem ms) M2B_KEY
  (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY) kk HyT ltac:(lia)
  ltac:(intros b Hb; rewrite HspT; unfold M2B_KEY, ESTACK in *; lia))
as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
assert (Hsx : src_ok rsegs W2 (ms_regs ms) (ms_mem ms) x (kk + 1)).
{ intros a Ha. destruct Hcx as (Hc1 & Hc2 & _). split.
  - destruct (Z.eq_dec (a - x) (Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb)))) as [He|He].
    + replace a with (x + Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb))) by lia.
      rewrite Hc2. discriminate.
    + replace a with (x + (a - x)) by lia. rewrite (Hc1 (a - x) ltac:(lia)). discriminate.
  - rewrite HspT. unfold ESTACK. lia. }
eapply SRr_bind.
{ eapply (aj_strcmp_at rsegs B LAWS ck_segs_low M2B_STRCMP (ASTRCMP fx2) W2 (ms_regs ms) (ms_mem ms)
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 _ (x_k rsegs cx)
    x M2B_KEY kk c1 c2 (q_R (x_e rsegs cx) - x_sp0 rsegs cx) (w64 0x82c68)
    ltac:(eassumption) R10' R11' Hx0 Hy0 ltac:(lia) ltac:(lia) ltac:(lia) Hmeet
    ltac:(rewrite HspT; lia));
  [ (* o mod 16 = 0 *)
    replace (q_R (x_e rsegs cx) - x_sp0 rsegs cx)
      with (q_R (x_e rsegs cx) + (-1) * x_sp0 rsegs cx) by lia;
    rewrite Zplus_mod, Zmult_mod, HR16, Hsp16; reflexivity
  | lia
  | unfold ESTACK; lia
  | (* gp *) etransitivity; [exact (CL 3%bv ltac:(m2kcb_in))|];
    etransitivity; [exact ((proj1 (proj2 Hcore)) 3 ltac:(lia))|]; exact Hgp
  | (* tp *) etransitivity; [exact (CL 4%bv ltac:(m2kcb_in))|];
    etransitivity; [exact ((proj1 (proj2 Hcore)) 4 ltac:(lia))|]; exact Htp
  | exact R1'
  | vm_compute; reflexivity
  | exact Hsx | exact Hsy
  | intros a Ha; unfold ESTACK; lia
  | intros a Ha; unfold M2B_KEY, ESTACK in *; lia
  | exact (amem_range_sub x 46 (kk + 1) ltac:(lia) Hmx46)
  | exact Hmy
  | exact (range_addressable_sub _ _ x 46 (kk + 1) ltac:(lia) Hrx46)
  | exact (shadow_hull_vis_sub _ x 46 (kk + 1) ltac:(lia) Hhx46)
  | exact Hry | exact Hhy ]. }
cbv beta. intros W' c' _ (-> & regsR & memR & mdR & -> & HJR & HPR & Hsame & HR10 & HK2 & _).
(* the state at 0x82c68: a0 = the wrapper's answer, the callee-saved registers and the spills as at the call *)
assert (HcoreR : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regsR memR mdR).
{ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 W2 regsR memR mdR HcoreT HJR);
  [ intros r Hr; apply HPR; unfold acallee_saved; lia
  | reflexivity | apply Permutation_refl | exact Hsame | apply (mo_le_refl MT MTL) |].
  intros a Ha Hs _. apply HK2; [exact Ha|].
  rewrite HspR in Hs. unfold T_SEG_STK, ASTACK in Hs. unfold ESTACK. lia. }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a ->
  aview rsegs (w_H W2) memR a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hz. rewrite (HK2 a Ha ltac:(unfold m2kb_wz, T_SEG_STK, ASTACK, ESTACK in *; lia)).
  exact (KT a Ha Hz). }
assert (HLR : cs_eq m2kcb_L regs2 regsR).
{ apply (cs_eq_trans _ _ (ms_regs ms)); [exact CL|].
  exact (cs_eq_of_pres m2kcb_L _ _ m2kcb_L_cs HPR). }
apply (m2kcb_tail cx POST at0 m fx2 rec kb ly2 S2 W2 regs2 mem2 md2 regsR memR mdR (strcmp_res c1 c2)
  Hpre HO (HKV rec) HKM HcoreR HLR).
- (* s9 = m + 2, saved over the call *)
  etransitivity; [exact (HPR 25 ltac:(unfold acallee_saved; lia))|]. exact R25'.
- exact HR10.
- exact (m2kcb_res_range c1 c2).
- exact Hres.
- eapply (val_mem_kept rsegs); [|exact T140]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T150]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T158]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T160]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- exact KR.
Qed.
End k.

About m2kb_key.
Print Assumptions m2kb_key.
