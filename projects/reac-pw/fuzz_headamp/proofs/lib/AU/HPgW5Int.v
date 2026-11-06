(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 1d255703e88 (m2_stack,
   m2_pre_call, m2_core_step, m2_core_call) and proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e88
   (m2t_garr8_kept, the run-to-call / contract / return pattern of tl_s4 .. tl_s6) for reac-pw/fuzz_rate's image-A
   list segment M03: rate's cut vocabulary (lib/A/RtPgSeg.v, rt_ / q_ names); the seam is generic in the segment's
   write set and carries rt_cpost_g's O conjunct; the walk of C6 -> C7 (memset, reac_rate_drivable_csv, check_csv)
   is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW14Csv.v, with its module paths and module names changed; 1191 of its 1275 lines of code are new or changed and 617 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v and RPgW5IntP.v at 164759458cd (one
   file); module paths changed, the w5_ / rs_ / rm_ / rl_ prefixes renamed (hw5_ / hsu_ / hm_ / hd_), the code walked
   anew on image B of fuzz_headamp (scope stores of e42, the runtime's memset on e42, the three words of e42, the call
   of the out-of-line pod_write_ent under PweSpec.pod_write_ent_specX, the tail and the scope-out stores), the
   AR_laws Section hypothesis replaced by the kernel theorem YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the Int-7 value pod of one
   property, SELI 0x828ec -> LATCH 0x82ae4, in LLVMFuzzerTestOneInput (0x80c40; pod.h:412-420), and the piece lemma
   of lib/AU/HPgSeg.v's hsu_piece_W5_int_stmt at headamp_himg_B / headamp_bld_B. Proves no function (kind: segment
   lemma).

   THE CODE (0x828ec .. 0x829cc and the slow block 0x82b54)
     0x828ec-0x8291c  thirteen `sb zero,48..60(s3)`: e42's granules in scope (HPgSteps.hdu_scope_e42_in)
     0x82920-0x8293c  a2 := 0x5c, a0 := R+0x60 (= e42 + 12), a1 := 0, s2 := t0, s4 := t3, s7 := a4, s5 := t2,
                      `jal` the runtime's memset 0x52228 (e42 + 12 .. e42 + 104 := 0)            (run A, then the call)
     0x82940-0x8295c  a1 := R+0x68 (= e42), `sw` 4 at e42, 4 at e42 + 4, 7 at e42 + 8 (a frame object: no check),
                      a0 := R+0x148 (= pp), `jal pod_write_ent` 0x84634                     (run B, then the call)
     0x82960-0x82990  a7 := s5, a3 := s7, t3 := s4, t0 := s2, a0 := R+0x140 (first); if first <> 0: a0 := R+0x78
                      (= pp + 0x400c), its shadow check (slow block 0x82b54), `sw s10` (= 1) there; a0 := -8 (run C)
     0x82994-0x829c8  thirteen `sb a0,48..60(s3)` and s7 := -8: e42 out of scope (HPgSteps.hdu_scope_e42_out)
     0x829cc          `j` 0x82ae4                                                                  (run D)
   REGISTERS the piece reads: sp, gp, tp, s1 = R, s3 = (F >> 3) + K, s10 = 1, s11 = K, t0, t2, t3, a4; it writes ra,
   t0 .. t2, a0 .. a7, s2, s4, s5, s7, t3 .. t6 (hw5i_clob) and leaves at LATCH t0 = |ps|, a3 = seen, a7 = the
   cursor, t3 = what is left, s7 = -8. R-RELATIVE CELLS it reads: R+0x60, R+0x68, R+0x78, R+0x140, R+0x148; it
   writes none. MEMORY it writes: e42 [F+0x180, F+0x1e8) and its 13 shadow bytes, the 16 bytes of the value pod at
   pp + at and the len cell (by pod_write_ent), has_params at pp + 0x400c when first is set.

   THE WALK. The two scope sites are HPgSteps' site lemmas; the four runs are the kit engine's (lib/Reusable YCbq
   aj_run_to_tok over HPgW5Kit.hw5_tbl), each from a fresh entry state; the memset call is the runtime's contract
   (the Section hypothesis HW5_AMEMSET), the pod_write_ent call the image-independent contract
   PweSpec.pod_write_ent_specX (the Section hypothesis PWE), each premise supplied at the call: e42 is a granule-aligned
   object of the frame for locals (F mod 32 = 0), in scope after the scope stores, apart from pp's block and from the
   callee's stack below R; pp's len cell holds at = |pc_buf ps| + 8 (8-aligned, at + 16 <= 5440). The value pod
   e42 holds is Layout.ent_mem (Ent 4 4 (le32 7)), whose pod_write_ent encoding is Model.enc_val (PInt 7). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW5Kit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps PweSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ======================================== the piece's registers, pod and write set ======================================== *)
Definition hw5i_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 28; 29; 30; 31]%bv.
Definition hw5i_clobA : list (bv 5) := [1; 10; 11; 12; 18; 20; 21; 23]%bv.
Definition hw5i_clobB : list (bv 5) := [1; 10; 11]%bv.
Definition hw5i_clobC : list (bv 5) := [5; 10; 11; 12; 13; 17; 28]%bv.
(* the value pod of an Int-7 property (Model.enc_val (PInt 7) = Model.enc_pod hw5i_e7) *)
Definition hw5i_e7 : Model.ent := Model.Ent POD_INT 4 (le32 7).
(* the bytes the piece writes: e42, its shadow granules, the value pod, the len cell and (first) has_params *)
Definition hw5i_E (F pp atv fsv : Z) (a : Z) : Prop :=
  (F + 0x180 <= a < F + 0x180 + 104) \/ (shadow_addr F + 48 <= a < shadow_addr F + 61) \/
  (pp + atv <= a < pp + atv + 16) \/ (pp + 0x4000 <= a < pp + 0x4008) \/
  (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010).
(* the first-flag the piece reads: set only on a params property while no params property was written *)
Definition hw5i_ifst (sel : Z) (ps : list (Z * pval)) : Z := if sel mod 4 =? 0 then 0 else hsu_first ps.

(* atoms 32 = K, 33 = e42 = F + 0x180, 34 = pp *)
Definition hw5i_extra (F pp : Z) : list word := [w64 HW5_SB; w64 (F + 0x180); w64 pp].

(* ---- run A, the start state at 0x82920 ---- *)
Definition ha_ov : list (bv 5 * sv) := [((2%bv : bv 5), SOff 9 0); ((27%bv : bv 5), hw5_Bx)].
Definition ha_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x150 0 0 [YP09.mkChunk 0x60 (CVal 8 (SOff 33 12))].
Definition ha_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF HW5_SB HW5_SB 0);
           (33%nat, mkAF 4096 140737479966720 3)] [] [].
Definition ss_ha : sstate := mkSS 0x82920 (hw5_sr ha_ov) [ha_slots] None ha_facts.
(* ---- run B, the start state at the memset's return address 0x82940 ---- *)
Definition hb_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x150 0 0
   [YP09.mkChunk 0x68 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 34 0))].
Definition hb_e42 : YP09.region := YP09.mkRegion (Some 33%nat) 0 12 0 12 [].
Definition hb_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF HW5_SB HW5_SB 0);
           (33%nat, mkAF 4096 140737479966720 3); (34%nat, mkAF 4096 140737479966720 4)] [] [].
Definition ss_hb : sstate := mkSS 0x82940 (hw5_sr ha_ov) [hb_slots; hb_e42] None hb_facts.
Definition hb_SH : list shent := [mkSHE 33 0 12].
(* ---- run C, the start state at pod_write_ent's return address 0x82960 ---- *)
Definition hc_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((27%bv : bv 5), hw5_Bx); ((26%bv : bv 5), SLit 1)].
Definition hc_slots (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x150 0 0
   [YP09.mkChunk 0x140 (CVal 8 (SLit f)); YP09.mkChunk 0x78 (CVal 8 (SOff 34 0x400c))].
Definition hc_flag (f : Z) : YP09.region := YP09.mkRegion (Some 34%nat) 0x400c 0x4010 0x400c (0x400c + 4 * f) [].
Definition hc_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF HW5_SB HW5_SB 0);
           (34%nat, mkAF 4096 140737479966720 4)] [] [].
Definition ss_hc (f : Z) : sstate := mkSS 0x82960 (hw5_sr hc_ov) [hc_slots f; hc_flag f] None hc_facts.
Definition hc_SH : list shent := [mkSHE 34 0x400c 0x4014].
(* ---- run D, the start state at 0x829cc ---- *)
Definition ss_hd : sstate := mkSS 0x829cc (hw5_sr []) [] None (mkFacts [] [] []).

(* ======================================== helpers ======================================== *)
Lemma hw5i_mod8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. rewrite (Z.div_mod x 32) by lia. rewrite H, Z.add_0_r.
replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by ring. apply Z.mod_mul. lia.
Qed.
Lemma hw5i_mod16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. rewrite (Z.div_mod x 32) by lia. rewrite H, Z.add_0_r.
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by ring. apply Z.mod_mul. lia.
Qed.
Lemma hw5i_m16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. rewrite (Z.div_mod x 16) by lia. rewrite H, Z.add_0_r.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by ring. apply Z.mod_mul. lia.
Qed.
Lemma hw5i_add8 : forall x c, x mod 8 = 0 -> c mod 8 = 0 -> (x + c) mod 8 = 0.
Proof. intros x c Hx Hc. rewrite Z.add_mod by lia. rewrite Hx, Hc. reflexivity. Qed.
Lemma hw5i_fl8 : forall x, x - 7 <= x / 8 * 8 <= x.
Proof. intros x. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.
Lemma hw5i_sh_add : forall F c, F mod 8 = 0 -> shadow_addr (F + c) = shadow_addr F + c / 8.
Proof.
intros F c H. unfold shadow_addr. rewrite (Z.div_mod F 8) at 1 by lia. rewrite H, Z.add_0_r.
rewrite (Z.add_comm (8 * (F / 8))), Z.mul_comm, Z.div_add by lia. lia.
Qed.
Lemma hw5i_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* the value of a register in a final symbolic state, over atoms the run's environment keeps *)
Lemma hw5i_reg_val : forall E Ef sr (regs : bvmap 5 word) (r : bv 5) v,
regs_ok Ef sr regs -> env_agree 35 E Ef -> sr_get sr r = v -> sv_atoms_lt 35 v = true ->
getr regs r = sv_denot E v.
Proof. intros E Ef sr regs r v HR HA Hv Hl. rewrite (HR r), Hv. apply (sv_denot_agree 35 E Ef v HA Hl). Qed.
Lemma hw5i_notin : forall (clob : list (bv 5)) (r : bv 5), existsb (fun c => bv_eqb c r) clob = false -> ~ In r clob.
Proof.
intros clob r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) clob = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite H in Ht. discriminate.
Qed.
Lemma hw5i_incl : forall (c1 c2 : list (bv 5)),
forallb (fun c => existsb (fun d => bv_eqb d c) c2) c1 = true -> forall r, ~ In r c2 -> ~ In r c1.
Proof.
intros c1 c2 Hb r Hn Hin. apply Hn. rewrite forallb_forall in Hb. specialize (Hb r Hin).
apply existsb_exists in Hb as (d & Hd & Hb). apply bv_eqb_eq in Hb. subst d. exact Hd.
Qed.
Definition hw5i_csb (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma hw5i_csb_ok : forall z, hw5i_csb z = true -> acallee_saved z.
Proof.
intros z H. unfold hw5i_csb in H. unfold acallee_saved.
repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
(* a register outside the piece's clobber list is one every callee preserves *)
Lemma hw5i_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn.
assert (HB : forallb (fun c : bv 5 => existsb (fun d => bv_eqb d c) hw5i_clob || hw5i_csb (bv_unsigned c))
  HPgSteps.nz_regs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB r (HPgSteps.in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply hw5i_csb_ok. exact Hq.
Qed.
Lemma hw5i_pres : forall (regsT regs2 : bvmap 5 word) (r : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r.
Proof. intros regsT regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac hw5i_cs := apply hw5i_csb_ok; vm_compute; reflexivity.
Ltac hw5i_nc := first [vm_compute; lia | apply hw5i_notin; vm_compute; reflexivity].

(* ---- the model of one Int-7 property (Model.prop_step's second and third arms) ---- *)
Lemma hw5i_img_int_eq : forall sh ps sel, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(hsu_key_of sel, PInt 7)]) None) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) ++ enc_pod hw5i_e7)
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None) || (hw5i_ifst sel ps =? 1))
  (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps sel Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_prop.
replace (prop_bytes sh (hsu_key_of sel, PInt 7)) with (le32 (hsu_key_of sel) ++ le32 0 ++ enc_pod hw5i_e7)
  by (unfold prop_bytes; replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh); reflexivity).
rewrite <- !app_assoc.
unfold has_params, params_struct, pc_ents, hw5i_ifst, hsu_key_of. cbn [p_props pc_props pc_open].
rewrite first_params_app. cbn [fst snd].
destruct (Z.eqb_spec (sel mod 4) 0) as [E4|E4].
- destruct (first_params ps) as [v|]; [destruct v|]; reflexivity.
- cbv beta iota. destruct (Z.eqb_spec (hsu_first ps) 1) as [E|E].
  + rewrite (hw5_first1 ps E). reflexivity.
  + destruct (hw5_first0 ps E) as [v Hv]. rewrite Hv. destruct v; reflexivity.
Qed.
Lemma hw5i_seen_int : forall ps sel,
hsu_seen (ps ++ [(hsu_key_of sel, PInt 7)]) = if sel mod 4 =? 0 then hsu_seen ps else 1.
Proof.
intros ps sel. unfold hsu_seen, hsu_key_of. rewrite existsb_app. cbn [existsb fst].
destruct (Z.eqb_spec (sel mod 4) 0) as [E|E]; cbn; [rewrite orb_false_r | rewrite orb_true_r]; reflexivity.
Qed.
Lemma hw5i_wf_int : forall sh ps sel, hsu_wf sh ps -> (length ps <= 2)%nat ->
hsu_wf sh (ps ++ [(hsu_key_of sel, PInt 7)]).
Proof.
intros sh ps sel (Hs & Hk & He & Hl) H2.
assert (HK : 0 <= hsu_key_of sel < 2 ^ 32)
  by (unfold hsu_key_of; destruct (sel mod 4 =? 0); split; try lia; apply Z.ltb_lt; reflexivity).
split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [split; [exact HK | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn [flat_map snd]; rewrite !app_nil_r; exact He|].
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma hw5i_loop_int : forall sh ps sel rest r, sh <> 7 ->
ps = fst (props_loop sh (length ps) (hsu_r0 rest)) ->
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))) ->
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) ->
(ps ++ [(hsu_key_of sel, PInt 7)], r) = props_loop sh (length (ps ++ [(hsu_key_of sel, PInt 7)])) (hsu_r0 rest).
Proof.
intros sh ps sel rest r Hsh Hps Hs1 H4.
rewrite length_app. cbn [length]. rewrite Nat.add_1_r. rewrite props_loop_S_end.
remember (props_loop sh (length ps) (hsu_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs1. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs1. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
unfold hsu_key_of. destruct (Z.eqb_spec (sel mod 4) 0) as [E|E]; [reflexivity|].
destruct H4 as [X|X]; [exfalso; exact (E X)|]. rewrite X. reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's memset entry in image B (__asan_memset 0x52228), discharged at the harness level *)
Hypothesis HW5_AMEMSET : aintrin_realizes rsegs B OSet 0x52228.
(* pod_write_ent, out of line in image B at 0x84634 *)
Hypothesis PWE : PweSpec.pod_write_ent_specX rsegs B MT 0x84634.

(* ======================================== memory helpers ======================================== *)
(* the frame address a journal's layout gives is the start layout's *)
Lemma hw5i_fa : forall {STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k} cid pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k cid pos HJ. destruct HJ as (_ & Hly & _).
unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
(* bytes a val_mem names, carried over a memory that keeps them *)
Lemma hw5i_val_kept : forall H mem H' mem' a n v,
val_mem rsegs (mrestrict H mem) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' mem' x = aview rsegs H mem x) ->
val_mem rsegs (mrestrict H' mem') a n v.
Proof.
intros H mem H' mem' a n v V K. apply hm_val_of_bytes. eapply hm_bytes_kept; [apply hm_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.
(* the frame's shadow bytes lie apart from every application range *)
Lemma hw5i_sep_sh : forall F x n i, 0 <= F -> F + 1024 <= 140737479966720 -> in_app x n -> 0 <= n -> 0 <= i < 128 ->
~ (x <= shadow_addr F + i < x + n).
Proof.
intros F x n i HF0 HF1 Hx Hn Hi. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hx.
unfold shadow_addr, SHADOW_OFF.
assert (Hq : F / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (Hq0 : 0 <= F / 8) by (apply Z.div_pos; lia).
lia.
Qed.
Lemma hw5i_sh_bounds : forall F, 0 <= F -> F + 1024 <= 140737479966720 ->
0 <= shadow_addr F /\ shadow_addr F + 128 <= 17594332446848.
Proof.
intros F HF0 HF1. unfold shadow_addr, SHADOW_OFF.
assert (Hq : F / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (Hq0 : 0 <= F / 8) by (apply Z.div_pos; lia).
lia.
Qed.
(* the shadow hull of bytes of e42 lies in the frame's shadow bytes *)
Lemma hw5i_hull_e42 : forall H mem F pat o n, hd_fsh rsegs H mem F pat -> (116 <= length pat)%nat -> F mod 8 = 0 ->
0 <= o -> o + n <= 104 -> 0 < n -> shadow_hull_vis (aview rsegs H mem) (F + 0x180 + o) n.
Proof.
intros H mem F pat o n P Hl HF Ho Hon Hn s Hs.
replace (F + 0x180 + o) with (F + (0x180 + o)) in Hs by lia.
replace (F + (0x180 + o) + n - 1) with (F + (0x180 + o + n - 1)) in Hs by lia.
rewrite !(hw5i_sh_add F) in Hs by exact HF. unfold hd_fsh in P.
set (y := shadow_addr F) in *.
assert (D1 : 48 <= (0x180 + o) / 8) by (apply Z.div_le_lower_bound; lia).
assert (D2 : (0x180 + o + n - 1) / 8 < 61) by (apply Z.div_lt_upper_bound; lia).
pose proof (hw5i_fl8 (y + (0x180 + o) / 8)) as L1.
pose proof (hw5i_fl8 (y + (0x180 + o + n - 1) / 8)) as L2.
assert (Hi : 0 <= s - y < Z.of_nat (length pat)) by lia.
replace s with (y + (s - y)) by lia. rewrite (P (s - y) Hi). discriminate.
Qed.
Lemma hw5i_amem_F : forall F a n, in_app F 1024 -> F <= a -> 0 <= n -> a + n <= F + 1024 -> amem_range a n.
Proof.
intros F a n HA H1 H2 H3. pose proof (@alloc_ceiling_value rc) as ([AC1 AC2] & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HA. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
Qed.
(* three words read back as twelve bytes *)
Lemma hw5i_word3 : forall H mem a x y z,
val_mem rsegs (mrestrict H mem) (a + 0) 4 x -> val_mem rsegs (mrestrict H mem) (a + 4) 4 y ->
val_mem rsegs (mrestrict H mem) (a + 8) 4 z ->
hm_bytes rsegs H mem a (Z_to_le_bytes 4 x ++ Z_to_le_bytes 4 y ++ Z_to_le_bytes 4 z).
Proof.
intros H mem a x y z V0 V4 V8. rewrite Z.add_0_r in V0.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
replace (a + 4 + 4) with (a + 8) by lia. apply hm_bytes_of_val. exact V8.
Qed.
(* a byte of the frame for locals is the journal's to write *)
Lemma hw5i_awr_F : forall STK sp0 FP bl0 blc ly own pos a,
In (4, pos) own -> frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024 ->
awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right. right. right. exists 4, pos. split; [exact Hown|].
left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. exact Ha.
Qed.

(* ======================================== the memset call ========================================
   YCbq's aj_intrin_at at op OSet, pc 0x52228, keeping same_io of the models (the contract's
   same_but_materialized), which the piece's post needs. *)
Lemma hw5i_memset_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 0x52228) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
  ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
  aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
  (forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = Some (x mod 256)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
    aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof using HW5_AMEMSET.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_segs_low as Hsl.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg Hbud);
  [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (HW5_AMEMSET lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS Hsl STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact (same_io_materialized _ _ Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff | exact Hfr].
Qed.

(* ======================================== run A: 0x82920 -> the memset's entry ======================================== *)
Lemma hw5i_runA : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pp : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x60) 8 (F + 0x180 + 12) ->
  70368744177664 <= R <= 140737488355328 -> R mod 16 = 0 ->
  4096 <= F -> F + 1024 <= 140737479966720 -> (F + 0x180) mod 8 = 0 -> 0 <= pp < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs 0x82920 regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regsT memT mdT,
      c2 = mkCfg (mkst regsT (Z_to_bv 64 0x52228) memT (seg_rom rsegs)) mdT /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
      (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobA -> getr regsT r = getr regs r) /\
      getr regsT 1 = w64 0x82940 /\ getr regsT 10 = w64 (F + 0x180 + 12) /\ getr regsT 11 = w64 0 /\
      getr regsT 12 = w64 92 /\ getr regsT 18 = getr regs 5 /\ getr regsT 20 = getr regs 28 /\
      getr regsT 21 = getr regs 7 /\ getr regsT 23 = getr regs 14 /\
      (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp HJ H2 H9 H27 V60 HRr HR16 HF1 HF2 HF8 Hpp.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
set (E := Ereg regs (hw5i_extra F pp)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (F + 0x180)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HE : E = Ereg regs (hw5i_extra F pp)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 0x180) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (hw5_sr ha_ov) regs).
{ apply (hw5_regs_ok E regs (hw5i_extra F pp)); [exact HE|]. unfold ha_ov.
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E ha_facts).
{ split; [| split; [exact I | exact I]].
  cbn [ha_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ]. }
assert (HS : st_ok rsegs E ss_ha (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82920) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ha. apply (hw5_entry rsegs _ _ regs (hw5i_extra F pp) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold ha_slots. apply Forall_cons; [|apply Forall_nil].
    apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs E _ R 0x60 8 (SOff 33 12) (F + 0x180 + 12));
      [ rewrite (hw5_den_off E 33 (F + 0x180) 12 E33) by lia; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | lia | exact V60 ].
  - unfold ha_slots; cbn [pairwise_disjoint all_disjoint]; repeat split; try exact I.
  - exact HFK. }
unfold cfg_at; change (w64 0x82920) with (Z_to_bv 64 0x82920).
aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x52228.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (hw5_regs_kept E Ef 35 (hw5_sr ha_ov) (ss_regs ssf) regs (ms_regs msf) hw5i_clobA HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [rewrite (hw5i_reg_val E Ef _ _ 1%bv (SLit 534848) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 10%bv (SOff 33 12) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (hw5_den_off E 33 (F + 0x180) 12 E33 ltac:(lia) ltac:(lia))|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 11%bv (SLit 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 12%bv (SLit 92) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 18%bv (SOff 5 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 5 5%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 20%bv (SOff 28 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 28 28%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 21%bv (SOff 7 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 7 7%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 23%bv (SOff 14 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 14 14%bv eq_refl)|];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val] in Hb; lia | ]);
  destruct Hr
  end.
Qed.

(* ======================================== run B: 0x82940 -> pod_write_ent's entry ======================================== *)
Lemma hw5i_runB : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pp : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x68) 8 (F + 0x180) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  (forall a, F + 0x180 <= a < F + 0x180 + 12 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x180) 12 -> in_app F 1024 ->
  70368744177664 <= R <= 140737488355328 -> R mod 16 = 0 ->
  4096 <= F -> F + 1024 <= 140737479966720 -> (F + 0x180) mod 8 = 0 -> F + 0x180 + 12 <= R ->
  4096 <= pp <= 140737479966720 -> pp mod 16 = 0 ->
  SRr rsegs W (cfg_at rsegs 0x82940 regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regsT memT mdT,
      c2 = mkCfg (mkst regsT (Z_to_bv 64 0x84634) memT (seg_rom rsegs)) mdT /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
      (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobB -> getr regsT r = getr regs r) /\
      getr regsT 1 = w64 0x82960 /\ getr regsT 10 = w64 pp /\ getr regsT 11 = w64 (F + 0x180) /\
      hm_bytes rsegs (w_H W) memT (F + 0x180) (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x180 <= a < F + 0x180 + 12) ->
        aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp HJ H2 H9 H27 V68 V148 Hawr Hra42 FApp
  HRr HR16 HF1 HF2 HF8 HFR Hpp Hp16.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
set (E := Ereg regs (hw5i_extra F pp)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (F + 0x180)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HE : E = Ereg regs (hw5i_extra F pp)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx hb_SH E (mrestrict (w_H W) memc)).
{ assert (UB : U E hw5_Bx = SHADOW_OFF)
    by (unfold hw5_Bx; rewrite (U_atom E 32 HW5_SB E32) by (unfold HW5_SB; lia); reflexivity).
  assert (UN : U E (SOff 33 0) = F + 0x180) by (apply U_atom; [exact E33 | lia]).
  constructor; [|constructor].
  split; cbn [she_m she_lo she_hi].
  - rewrite UB, UN. rewrite <- aview_rd_of. replace (F + 0x180 + 0) with (F + 0x180) by lia.
    replace (12 - 0) with 12 by lia. exact Hra42.
  - unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
    rewrite Z.min_l, Z.max_r in Ha by lia. unfold in_app, kLowShadowBeg, kHighMemBeg in FApp. unfold SHADOW_OFF. lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 0x180) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (hw5_sr ha_ov) regs).
{ apply (hw5_regs_ok E regs (hw5i_extra F pp)); [exact HE|]. unfold ha_ov.
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E hb_facts).
{ split; [| split; [exact I | exact I]].
  cbn [hb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ]. }
assert (HS : st_ok rsegs E ss_hb (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82940) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_hb. apply (hw5_entry rsegs _ _ regs (hw5i_extra F pp) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold hb_slots, hb_e42. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x68 8 (SOff 33 0) (F + 0x180));
          [ rewrite (hw5_den_off E 33 (F + 0x180) 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V68 ].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 34 0) pp);
          [ rewrite (hw5_den_off E 34 pp 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V148 ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 (F + 0x180));
        [ exact U33 | lia | lia
        | intros o Ho; exact (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (F + 0x180 + o) HJ
                                      (Hawr (F + 0x180 + o) ltac:(lia))))
        | apply Forall_nil ].
  - unfold hb_slots, hb_e42; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 0x82940) with (Z_to_bv 64 0x82940).
aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x84634.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (F + 0x180));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha; apply Hawr; lia | ] ]).
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (hw5_regs_kept E Ef 35 (hw5_sr ha_ov) (ss_regs ssf) regs (ms_regs msf) hw5i_clobB HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [rewrite (hw5i_reg_val E Ef _ _ 1%bv (SLit 534880) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 10%bv (SOff 34 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (hw5_den_off E 34 pp 0 E34) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 11%bv (SOff 33 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (hw5_den_off E 33 (F + 0x180) 0 E33) by lia; rewrite Z.add_0_r; reflexivity|];
  assert (F33 : ew Ef 33 = ew E 33) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Re := fresh "Re" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Re _];
  let Ce := fresh "Ce" in
  destruct Re as (_ & _ & _ & Ce);
  cbn [r_chunks r_base base_val] in Ce;
  try rewrite F33 in Ce; rewrite U33 in Ce;
  rewrite Forall_forall in Ce;
  split;
  [ apply hw5i_word3;
    [ apply (val_of_chunk_ok rsegs Ef _ (F + 0x180) 0 4 (SLit 4) 4)
    | apply (val_of_chunk_ok rsegs Ef _ (F + 0x180) 4 4 (SLit 4) 4)
    | apply (val_of_chunk_ok rsegs Ef _ (F + 0x180) 8 4 (SLit 7) 7) ];
    first [ apply Ce; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | (cbn; lia) | lia ]
  |];
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; first [lia | (apply Hn; lia)] | ]);
  destruct Hr
  end.
Qed.

(* ======================================== run C: 0x82960 -> 0x82994 ======================================== *)
Lemma hw5i_runC : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp fsv : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 26 = w64 1 -> getr regs 27 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  70368744177664 <= R <= 140737488355328 -> R mod 16 = 0 -> pp + 0x4010 <= R -> (fsv = 0 \/ fsv = 1) ->
  SRr rsegs W (cfg_at rsegs 0x82960 regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regsT memT mdT,
      c2 = mkCfg (mkst regsT (Z_to_bv 64 0x82994) memT (seg_rom rsegs)) mdT /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
      (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobC -> getr regsT r = getr regs r) /\
      getr regsT 10 = w64 (-8) /\ getr regsT 5 = getr regs 18 /\ getr regsT 13 = getr regs 23 /\
      getr regsT 17 = getr regs 21 /\ getr regsT 28 = getr regs 20 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010) ->
        aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a) /\
      (fsv = 1 -> hm_bytes rsegs (w_H W) memT (pp + 0x400c) (Z_to_le_bytes 4 1))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp fsv HJ Hpp Hfresh H2 H9 H26 H27
  V140 V78 HRr HR16 HPR Hfst.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
pose proof HJ as (HAR & _).
pose proof (@alloc_ceiling_value rc) as ([AC1 AC2] & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
set (E := Ereg regs (hw5i_extra 0 pp)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HE : E = Ereg regs (hw5i_extra 0 pp)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx hc_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 34 0x400c 0x4014 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U34 : bv_unsigned (ew E 34) = pp) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (hw5_sr hc_ov) regs).
{ apply (hw5_regs_ok E regs (hw5i_extra 0 pp)); [exact HE|]. unfold hc_ov.
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H26. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E hc_facts).
{ split; [| split; [exact I | exact I]].
  cbn [hc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U34.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ]. }
destruct Hfst as [-> | ->].
all: lazymatch goal with Vd : val_mem _ _ (_ + 0x140) 8 ?f |- _ =>
  assert (HS : st_ok rsegs E (ss_hc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82960) memc (seg_rom rsegs))));
  [ rewrite restrict_mkst_fx; unfold ss_hc; apply (hw5_entry rsegs _ _ regs (hw5i_extra 0 pp) E); [exact HE| | | | |];
    [ exact HR0
    | vm_compute; reflexivity
    | unfold hc_slots, hc_flag;
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |];
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        [ apply (chunk_ok_val rsegs E _ R 0x140 8 (SLit f) f);
            [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd ]
        | apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 34 0x400c) (pp + 0x400c));
            [ rewrite (hw5_den_off E 34 pp 0x400c E34) by lia; reflexivity
            | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ] ]
      | apply (hm_rw_region rsegs E (w_H W) memc 34 pp);
          [ exact U34 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | apply Forall_nil ] ]
    | unfold hc_slots, hc_flag; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [r_base r_lo r_hi base_val]; rewrite U9, U34; repeat split; try exact I; lia
    | exact HFK ]
  | ] end.
all: unfold cfg_at; change (w64 0x82960) with (Z_to_bv 64 0x82960).
all: aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82994.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat pp);
    [ reflexivity | exact U34
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (hw5_regs_kept E Ef 35 (hw5_sr hc_ov) (ss_regs ssf) regs (ms_regs msf) hw5i_clobC HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [rewrite (hw5i_reg_val E Ef _ _ 10%bv (SLit 18446744073709551608) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          apply bv_eq; vm_compute; reflexivity|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 5%bv (SOff 18 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 13%bv (SOff 23 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 17%bv (SOff 21 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)|];
  split; [rewrite (hw5i_reg_val E Ef _ _ 28%bv (SOff 20 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite hw5i_SOff0, HE; exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn2 := fresh "Hn2" in
    intros a Ha Hn2;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U34 in Hb;
       first [lia | (apply Hn2; split; [reflexivity | lia])] | ]);
    destruct Hr
  |];
  assert (F34 : ew Ef 34 = ew E 34) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rg := fresh "Rg" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rg _];
  let Cg := fresh "Cg" in
  destruct Rg as (_ & _ & _ & Cg);
  cbn [r_chunks r_base base_val] in Cg; try rewrite F34 in Cg; try rewrite U34 in Cg;
  rewrite Forall_forall in Cg;
  let Hf1 := fresh "Hf1" in intros Hf1;
  first
  [ discriminate Hf1
  | apply hm_bytes_of_val;
    apply (val_of_chunk_ok rsegs Ef _ pp 0x400c 4 (SLit 1) 1);
    [ apply Cg; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ] ]
  end.
Qed.

(* ======================================== run D: 0x829cc -> 0x82ae4 ======================================== *)
Lemma hw5i_runD : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  SRr rsegs W (cfg_at rsegs 0x829cc regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regsT memT mdT,
      c2 = mkCfg (mkst regsT (Z_to_bv 64 0x82ae4) memT (seg_rom rsegs)) mdT /\
      ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
      (forall r : bv 5, bv_unsigned r <> 0 -> getr regsT r = getr regs r) /\
      (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
set (E := Ereg regs [w64 HW5_SB]).
assert (HE : E = Ereg regs [w64 HW5_SB]) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HR0 : regs_ok E (hw5_sr []) regs) by (apply (hw5_regs_ok E regs [w64 HW5_SB]); [exact HE | apply Forall_nil]).
assert (HS : st_ok rsegs E ss_hd (restrict (w_H W) (mkst regs (Z_to_bv 64 0x829cc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_hd. apply (hw5_entry rsegs _ _ regs [w64 HW5_SB] E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at; change (w64 0x829cc) with (Z_to_bv 64 0x829cc).
aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82ae4.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
  cbn [ms_regs restrict] in HRf;
  split; [reflexivity|];
  exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in intros r Hr0;
    exact (hw5_regs_kept E Ef 35 (hw5_sr []) (ss_regs ssf) regs (ms_regs msf) [] HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 (fun H => H))
  |];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  destruct Hr
  end.
Qed.

(* ======================================== the core walk: SELI 0x828ec -> LATCH 0x82ae4 ======================================== *)
Definition hw5i_R (regs : bvmap 5 word) (F pp atv fsv : Z) :
  world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  hm_bytes rsegs (w_H W2) mem2 (pp + atv) (enc_pod hw5i_e7) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 16) /\
  (fsv = 1 -> hm_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Z_to_le_bytes 4 1)) /\
  hd_fsh rsegs (w_H W2) mem2 F headamp_B_shA /\
  getr regs2 5 = getr regs 5 /\ getr regs2 13 = getr regs 14 /\ getr regs2 17 = getr regs 7 /\
  getr regs2 28 = getr regs 28 /\ getr regs2 23 = w64 (-8).

Lemma hw5i_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv fsv pos : Z),
  ameter_laws MT ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  st_nev S + k <= EV_MAX ->
  In (4, pos) own -> F = frame_addr ly 4 pos ->
  hd_fsh rsegs (w_H W) memc F headamp_B_shA ->
  getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x60) 8 (F + 0x180 + 12) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x68) 8 (F + 0x180) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 16 <= 5440 -> atv mod 8 = 0 -> (fsv = 0 \/ fsv = 1) ->
  SRr rsegs W (cfg_at rsegs 0x828ec regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82ae4 hw5i_clob
      (hw5i_E F pp atv fsv) (hw5i_R regs F pp atv fsv)).
Proof using HW5_AMEMSET PWE.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv fsv pos MTL
  HJ Hpp Hfresh Hnev Hown HFa Hfsh H2 H3 H4 H9 H19 H26 H27 V60 V68 V78 V140 V148 Vlen HR32 HRlo HRhi Hat Hal Hal8 Hfst.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as ([AC1 AC2] & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTP : PweSpec.T_pwe_STK = 4144) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (Hpwe : PweSpec.pwe_len hw5i_e7 = 16) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & _).
rewrite Hrq, HPS in Hpceil, Happ.
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (HFc : frame_addr lyc 4 pos = F) by (rewrite HFa; exact (hw5i_fa 4 pos HJ)).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR HinF) as (FB1 & FB2 & FApp).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR HinF) as (F32 & _).
rewrite HFc in FB1, FB2, FApp, F32. change (fs_frame_bytes 4) with 1024 in FB2, FApp.
assert (HF8 : F mod 8 = 0) by (apply hw5i_mod8; exact F32).
assert (HQ8 : (F + 0x180) mod 8 = 0) by (apply hw5i_add8; [exact HF8 | reflexivity]).
assert (HR16 : R mod 16 = 0) by (apply hw5i_mod16; exact HR32).
assert (HPF : pp + 19744 <= F \/ F + 1024 <= pp).
{ pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ pp Layout.PP_SIZE 4 pos HAR Hpp HinF) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFc, Hrq, HPS in D. change (fs_frame_bytes 4) with 1024 in D.
  exact D. }
assert (HRb : alloc_ceiling + 16384 <= R) by lia.
assert (HRu : R + 0x220 <= 140737488355328) by lia.
pose proof (hw5i_sh_bounds F ltac:(lia) ltac:(lia)) as (SH0 & SHB).
assert (SPP : forall i, 0 <= i < 128 -> ~ (pp <= shadow_addr F + i < pp + 19744)).
{ intros i Hi. apply (hw5i_sep_sh F pp 19744 i); [lia | lia | exact Happ | lia | exact Hi]. }
assert (SFF : forall i, 0 <= i < 128 -> ~ (F <= shadow_addr F + i < F + 1024)).
{ intros i Hi. apply (hw5i_sep_sh F F 1024 i); [lia | lia | exact FApp | lia | exact Hi]. }
assert (LP0 : length headamp_B_shA = 116%nat) by reflexivity.
clear Hstk Hfrs.
(* ---- 1. e42 in scope ---- *)
eapply SRr_bind.
{ apply (HPgSteps.hdu_scope_e42_in B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 4 pos
    HJ Hown ltac:(lia));
  [ rewrite HFc; exact H19 | rewrite HFc; lia | rewrite HFc; lia | change (fs_frame_bytes 4 / 8) with 128; lia ]. }
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hk1 & Hfr1 & Hperm1 & Hio1 & Hmo1 & K1 & Z1).
rewrite HFc in K1, Z1.
assert (G1 : forall r : bv 5, bv_unsigned r <> 0 -> getr regs1 r = getr regs r) by (intros r Hr; exact (Hk1 r Hr (fun X => X))).
assert (Hpp1 : In (pp, Layout.PP_SIZE) (ablocks B ly1 S1)) by exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
assert (HF1 : frame_addr ly1 4 pos = F) by (rewrite HFa; exact (hw5i_fa 4 pos HJ1)).
(* the frame's shadow with e42 in scope *)
assert (PIN1 : hd_fsh rsegs (w_H W1) mem1 F (hmu_sh false false false false true false false false)).
{ replace (hmu_sh false false false false true false false false) with (hm_setn headamp_B_shA 48 13 0)
    by (vm_compute; reflexivity).
  apply (hm_fsh_set rsegs (w_H W) memc (w_H W1) mem1 F headamp_B_shA 48 13 0 Hfsh).
  - intros j Hj. apply Z1. change (Z.of_nat 48) with 48 in Hj. change (Z.of_nat (48 + 13)) with 61 in Hj. lia.
  - intros j Hj Hn. rewrite LP0 in Hj. change (Z.of_nat 48) with 48 in Hn. change (Z.of_nat (48 + 13)) with 61 in Hn.
    apply K1; [lia | lia]. }
(* ---- 2. run A ---- *)
eapply SRr_bind.
{ change (mkCfg (mkst regs1 (w64 0x82920) mem1 (seg_rom rsegs)) md1) with (cfg_at rsegs 0x82920 regs1 mem1 md1).
  apply (hw5i_runA STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R F pp HJ1).
  - rewrite G1 by (vm_compute; lia). exact H2.
  - rewrite G1 by (vm_compute; lia). exact H9.
  - rewrite G1 by (vm_compute; lia). exact H27.
  - apply (hw5i_val_kept (w_H W) memc); [exact V60|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply K1; lia.
  - lia.
  - exact HR16.
  - lia.
  - lia.
  - exact HQ8.
  - lia. }
intros W2 c2 _ (-> & regsA & memA & mdA & -> & HJA & HioA & HkA & A1 & A10 & A11 & A12 & A18 & A20 & A21 & A23 & KA).
assert (GA : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobA -> getr regsA r = getr regs r).
{ intros r Hr0 Hr. rewrite (HkA r Hr0 Hr). exact (G1 r Hr0). }
assert (PINA : hd_fsh rsegs (w_H W1) memA F (hmu_sh false false false false true false false false)).
{ apply (hm_fsh_kept rsegs (w_H W1) mem1 _ _ F _ PIN1). intros j Hj. rewrite hmu_sh_len in Hj. apply KA. lia. }
(* ---- 3. the memset call: e42 + 12 .. e42 + 104 := 0 ---- *)
eapply SRr_bind.
{ refine (hw5i_memset_at W1 regsA memA STK sp0 FP ly S W0 mem0 md0 own ly1 S1 mdA k (F + 0x180 + 12) 0 92 (R - sp0)
    (w64 0x82940) HJA A10 A11 A12 _ _ _ _ _ _ _ _ _ A1 _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite (GA 2%bv) by hw5i_nc. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite (GA 3%bv) by hw5i_nc. exact H3.
  - rewrite (GA 4%bv) by hw5i_nc. exact H4.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + apply (hw5i_awr_F _ _ _ _ _ _ _ pos a Hown). rewrite HF1. lia.
    + rewrite Hes. lia.
  - apply (hw5i_amem_F F); [exact FApp | lia | lia | lia].
  - replace (F + 0x180 + 12) with (F + HMU_E42 + 12) by (unfold HMU_E42; lia).
    exact (hmu_B_ra_e42 rsegs (w_H W1) memA F false false false false false false false 12 92 PINA HF8 ltac:(lia) ltac:(lia)).
  - intros _. apply (hw5i_hull_e42 (w_H W1) memA F _ 12 92 PINA); [rewrite hmu_sh_len; lia | exact HF8 | lia | lia | lia]. }
intros W3 c3 _ (-> & regsM & memM & mdM & -> & HJM & HioM & HPM & M10 & MZ & KM).
assert (GM : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobA -> acallee_saved (bv_unsigned r) ->
  getr regsM r = getr regs r).
{ intros r Hr0 Hr Hc. rewrite (hw5i_pres regsA regsM r HPM Hc). exact (GA r Hr0 Hr). }
assert (KMA : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x180 + 12 <= a < F + 0x180 + 104) -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W1) memM a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha Hn1 Hn2. rewrite KM; [apply KA; exact Ha | exact Ha | intros X; apply Hn1; lia | rewrite Hes; intros X; apply Hn2; lia]. }
assert (PINM : hd_fsh rsegs (w_H W1) memM F (hmu_sh false false false false true false false false)).
{ apply (hm_fsh_kept rsegs (w_H W1) mem1 _ _ F _ PIN1). intros j Hj. rewrite hmu_sh_len in Hj.
  apply KMA; [lia | intros X; apply (SFF j); lia | lia]. }
(* ---- 4. run B ---- *)
eapply SRr_bind.
{ change (mkCfg (mkst regsM (w64 0x82940) memM (seg_rom rsegs)) mdM) with (cfg_at rsegs 0x82940 regsM memM mdM).
  apply (hw5i_runB STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 memM mdM k regsM R F pp HJM).
  - rewrite GM by first [hw5i_nc | hw5i_cs]. exact H2.
  - rewrite GM by first [hw5i_nc | hw5i_cs]. exact H9.
  - rewrite GM by first [hw5i_nc | hw5i_cs]. exact H27.
  - apply (hw5i_val_kept (w_H W) memc); [exact V68|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    rewrite KMA by lia. apply K1; lia.
  - apply (hw5i_val_kept (w_H W) memc); [exact V148|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    rewrite KMA by lia. apply K1; lia.
  - intros a Ha. apply (hw5i_awr_F _ _ _ _ _ _ _ pos a Hown). rewrite HF1. lia.
  - replace (F + 0x180) with (F + HMU_E42 + 0) by (unfold HMU_E42; lia).
    exact (hmu_B_ra_e42 rsegs (w_H W1) memM F false false false false false false false 0 12 PINM HF8 ltac:(lia) ltac:(lia)).
  - exact FApp.
  - lia.
  - exact HR16.
  - lia.
  - lia.
  - exact HQ8.
  - lia.
  - lia.
  - exact Hp16. }
intros W4 c4 _ (-> & regsB & memB & mdB & -> & HJB & HioB & HkB & B1 & B10 & B11 & BE & KB).
assert (GB : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobA -> ~ In r hw5i_clobB ->
  acallee_saved (bv_unsigned r) -> getr regsB r = getr regs r).
{ intros r Hr0 Hr HrB Hc. rewrite (HkB r Hr0 HrB). exact (GM r Hr0 Hr Hc). }
assert (B2 : getr regsB 2 = w64 R) by (rewrite GB by first [hw5i_nc | hw5i_cs]; exact H2).
assert (B3 : getr regsB 3 = w64 (as_gp B)) by (rewrite GB by first [hw5i_nc | hw5i_cs]; exact H3).
assert (B4 : getr regsB 4 = w64 (as_tp B)) by (rewrite GB by first [hw5i_nc | hw5i_cs]; exact H4).
assert (SPB : spZ regsB = R) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
assert (KBA : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x180 <= a < F + 0x180 + 104) -> ~ (R - 4096 <= a < R) ->
  ~ (shadow_addr F + 48 <= a < shadow_addr F + 61) ->
  aview rsegs (w_H W1) memB a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn1 Hn2 Hn5. rewrite KB by (try exact Ha; intros X; apply Hn1; lia).
  rewrite KMA by (try exact Ha; try exact Hn2; intros X; apply Hn1; lia).
  apply K1; [exact Ha | exact Hn5]. }
(* e42 holds Layout.ent_mem hw5i_e7 *)
assert (EB : hm_bytes rsegs (w_H W1) memB (F + 0x180) (Layout.ent_mem hw5i_e7)).
{ change (Layout.ent_mem hw5i_e7) with (le32 4 ++ le32 4 ++ le32 7 ++ zeros 92).
  replace (le32 4 ++ le32 4 ++ le32 7 ++ zeros 92)
    with ((Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 7) ++ repeat (Z_to_bv 8 0) 92)
    by (rewrite <- !app_assoc; reflexivity).
  apply hm_bytes_app. split; [exact BE|].
  rewrite !length_app, !length_Z_to_le_bytes. change (Z.of_nat (4 + (4 + 4))) with 12.
  apply (hm_bytes_kept rsegs (w_H W1) memM).
  - apply hm_memset_bytes. intros j Hj. change (Z.of_nat 92) with 92 in Hj. exact (MZ j Hj).
  - intros y Hy. rewrite hm_length_repeat in Hy. change (Z.of_nat 92) with 92 in Hy. apply KB; lia. }
assert (PINB : hd_fsh rsegs (w_H W1) memB F (hmu_sh false false false false true false false false)).
{ apply (hm_fsh_kept rsegs (w_H W1) memM _ _ F _ PINM). intros j Hj. rewrite hmu_sh_len in Hj.
  apply KB; [lia | intros X; apply (SFF j); lia]. }
(* ---- 5. the call of pod_write_ent (pp, e42) ---- *)
pose proof (PweSpec.pwe_pp_of_block rsegs B ly1 S1 W1 memB mdB pp (proj1 HJB) Hpp1) as (P0 & P8 & P63 & Pam & Pra & Phull).
eapply SRr_bind.
{ change (mkCfg (mkst regsB (Z_to_bv 64 0x84634) memB (seg_rom rsegs)) mdB) with (cfg_at rsegs 0x84634 regsB memB mdB).
  apply (PWE STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 memB mdB k regsB pp (F + 0x180) atv hw5i_e7).
  - unfold PweSpec.pw_pre. split; [exact HJB|].
    split; [rewrite B1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite B1; unfold w64; rewrite unsigned_lit_small by lia; lia|].
    split; [exact B3|]. split; [exact B4|].
    rewrite SPB, HTP. split; [rewrite (hw5i_mod16 R HR32); reflexivity|]. split; [lia|]. split; [lia|]. exact Hnev.
  - exact B10.
  - exact B11.
  - exact P0.
  - exact P8.
  - exact P63.
  - exact Pam.
  - exact Pra.
  - exact Phull.
  - eapply PweSpec.pwe_awr_fresh; [exact Hpp1 | exact Hfresh | lia | rewrite Hpwe; unfold Layout.POD_BUF_MAX; lia].
  - left. rewrite SPB, HTP, HPS. lia.
  - apply (hw5i_val_kept (w_H W) memc); [exact Vlen|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    unfold Layout.OFF_LEN in Hx. apply KBA; [lia | lia | lia | intros X; apply (SPP (x - shadow_addr F)); lia].
  - lia.
  - exact Hal8.
  - rewrite Hpwe. unfold Layout.POD_BUF_MAX. lia.
  - lia.
  - exact HQ8.
  - unfold Layout.ENT_SIZE. apply (hw5i_amem_F F); [exact FApp | lia | lia | lia].
  - reflexivity.
  - unfold Layout.ENT_SIZE, hw5i_e7. cbn. lia.
  - unfold hw5i_e7, POD_INT. cbn. lia.
  - exact EB.
  - unfold Layout.ENT_SIZE. replace (F + 0x180) with (F + HMU_E42 + 0) by (unfold HMU_E42; lia).
    exact (hmu_B_ra_e42 rsegs (w_H W1) memB F false false false false false false false 0 104 PINB HF8 ltac:(lia) ltac:(lia)).
  - unfold Layout.ENT_SIZE. replace (F + 0x180) with (F + 0x180 + 0) by lia.
    apply (hw5i_hull_e42 (w_H W1) memB F _ 0 104 PINB); [rewrite hmu_sh_len; lia | exact HF8 | lia | lia | lia].
  - unfold Layout.ENT_SIZE. rewrite HPS. lia.
  - left. unfold Layout.ENT_SIZE. rewrite SPB, HTP. lia. }
intros W5 c5 _ (fx2 & ly3 & S3 & regs3 & mem3 & md3 & -> & Hfx & HJ3 & HP3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & K3 &
  (Benc & Vlen3 & _ & _ & _)).
subst fx2.
rewrite SPB, HTP in K3.
assert (Hpp3 : In (pp, Layout.PP_SIZE) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym Hperm3) Hpp1).
assert (G3 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw5i_clobA -> ~ In r hw5i_clobB ->
  acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs r).
{ intros r Hr0 Hr HrB Hc. rewrite (hw5i_pres regsB regs3 r HP3 Hc). exact (GB r Hr0 Hr HrB Hc). }
assert (K3A : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x180 <= a < F + 0x180 + 104) -> ~ (R - 4144 <= a < R) ->
  ~ (pp + atv <= a < pp + atv + 16) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  ~ (shadow_addr F + 48 <= a < shadow_addr F + 61) ->
  aview rsegs (w_H W5) mem3 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn1 Hn2 Hn3 Hn4 Hn5. rewrite K3; [| exact Ha | exact Hn2 |].
  - apply KBA; [exact Ha | exact Hn1 | intros X; apply Hn2; lia | exact Hn5].
  - unfold PweSpec.pwe_E. rewrite Hpwe. unfold Layout.OFF_LEN. intros [X|X]; [apply Hn3 | apply Hn4]; lia. }
(* ---- 6. run C ---- *)
eapply SRr_bind.
{ rewrite B1. change (mkCfg (mkst regs3 (w64 0x82960) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs 0x82960 regs3 mem3 md3).
  apply (hw5i_runC STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W5 mem3 md3 k regs3 R pp fsv HJ3 Hpp3 Hfresh).
  - rewrite G3 by first [hw5i_nc | hw5i_cs]. exact H2.
  - rewrite G3 by first [hw5i_nc | hw5i_cs]. exact H9.
  - rewrite G3 by first [hw5i_nc | hw5i_cs]. exact H26.
  - rewrite G3 by first [hw5i_nc | hw5i_cs]. exact H27.
  - apply (hw5i_val_kept (w_H W) memc); [exact V140|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply K3A; lia.
  - apply (hw5i_val_kept (w_H W) memc); [exact V78|]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply K3A; lia.
  - lia.
  - exact HR16.
  - lia.
  - exact Hfst. }
intros W6 c6 _ (-> & regsC & memC & mdC & -> & HJC & HioC & HkC & C10 & C5 & C13 & C17 & C28 & KC & CF).
assert (HF3 : frame_addr ly3 4 pos = F) by (rewrite HFa; exact (hw5i_fa 4 pos HJC)).
assert (C19 : getr regsC 19 = w64 (shadow_addr F)).
{ rewrite (HkC 19%bv) by hw5i_nc. rewrite G3 by first [hw5i_nc | hw5i_cs]. exact H19. }
(* ---- 7. e42 out of scope, s7 := -8 ---- *)
eapply SRr_bind.
{ change (mkCfg (mkst regsC (Z_to_bv 64 0x82994) memC (seg_rom rsegs)) mdC) with (cfg_at rsegs 0x82994 regsC memC mdC).
  apply (HPgSteps.hdu_scope_e42_out B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W5 memC mdC k regsC 4 pos
    HJC Hown ltac:(lia));
  [ rewrite HF3; exact C19 | exact C10 | rewrite HF3; lia | rewrite HF3; lia | change (fs_frame_bytes 4 / 8) with 128; lia ]. }
intros W7 c7 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hk4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & K4 & (Z4 & S7)).
rewrite HF3 in K4, Z4.
(* ---- 8. run D: the jump to LATCH ---- *)
eapply SRr_mono.
{ change (mkCfg (mkst regs4 (w64 0x829cc) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs 0x829cc regs4 mem4 md4).
  exact (hw5i_runD STK sp0 FP ly S W0 mem0 md0 own ly4 S4 W7 mem4 md4 k regs4 HJ4). }
intros W8 c8 _ (-> & regsD & memD & mdD & -> & HJD & HioD & HkD & KD).
(* ---- the post ---- *)
assert (KDC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 48 <= a < shadow_addr F + 61) ->
  aview rsegs (w_H W7) memD a = aview rsegs (w_H W5) memC a).
{ intros a Ha Hn. rewrite KD by exact Ha. apply K4; [exact Ha | exact Hn]. }
unfold hw5_post. exists ly4, S4, regsD, memD, mdD.
split; [reflexivity|].
split; [exact HJD|].
split.
{ intros r Hr0 Hr.
  assert (HrA : ~ In r hw5i_clobA) by exact (hw5i_incl hw5i_clobA hw5i_clob ltac:(vm_compute; reflexivity) r Hr).
  assert (HrB : ~ In r hw5i_clobB) by exact (hw5i_incl hw5i_clobB hw5i_clob ltac:(vm_compute; reflexivity) r Hr).
  assert (HrC : ~ In r hw5i_clobC) by exact (hw5i_incl hw5i_clobC hw5i_clob ltac:(vm_compute; reflexivity) r Hr).
  assert (Hr7 : ~ In r [23%bv]) by exact (hw5i_incl [23%bv] hw5i_clob ltac:(vm_compute; reflexivity) r Hr).
  rewrite (HkD r Hr0), (Hk4 r Hr0 Hr7), (HkC r Hr0 HrC).
  exact (G3 r Hr0 HrA HrB (hw5i_callee r Hr0 Hr)). }
split; [rewrite Hfr4, Hfr3; exact Hfr1|].
split; [eapply Permutation_trans; [exact Hperm4|]; eapply Permutation_trans; [exact Hperm3 | exact Hperm1]|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [exact HioA|].
  eapply same_io_trans; [exact HioM|]. eapply same_io_trans; [exact HioB|].
  eapply same_io_trans; [exact Hio3|]. eapply same_io_trans; [exact HioC|].
  eapply same_io_trans; [exact Hio4 | exact HioD]. }
split; [exact (mo_le_trans MT MTL _ _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Hmo1 Hmo3) Hmo4)|].
assert (SPR : spZ regs = R) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
split.
{ intros a Ha Hst Hn. rewrite SPR, HTS in Hst. unfold hw5i_E in Hn.
  rewrite KDC; [| exact Ha | intros X; apply Hn; right; left; exact X].
  rewrite KC; [| exact Ha | intros X; apply Hn; right; right; right; right; exact X].
  apply K3A; [exact Ha | intros X; apply Hn; left; exact X | intros X; apply Hst; lia
             | intros X; apply Hn; right; right; left; exact X | intros X; apply Hn; right; right; right; left; exact X
             | intros X; apply Hn; right; left; exact X]. }
unfold hw5i_R.
split.
{ apply (hm_bytes_kept rsegs (w_H W5) mem3); [exact Benc|].
  intros x Hx. change (Z.of_nat (length (enc_pod hw5i_e7))) with 16 in Hx.
  rewrite KDC; [| lia | intros X; apply (SPP (x - shadow_addr F)); lia].
  apply KC; [lia | intros (_ & X); lia]. }
split.
{ apply (hw5i_val_kept (w_H W5) mem3); [rewrite Hpwe in Vlen3; exact Vlen3|].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  rewrite KDC; [| lia | intros X; apply (SPP (x - shadow_addr F)); lia].
  apply KC; [lia | intros (_ & X); lia]. }
split.
{ intros Hf1. apply (hm_bytes_kept rsegs (w_H W5) memC); [exact (CF Hf1)|].
  intros x Hx. rewrite length_Z_to_le_bytes in Hx. change (Z.of_nat 4) with 4 in Hx.
  apply KDC; [lia | intros X; apply (SPP (x - shadow_addr F)); lia]. }
split.
{ replace headamp_B_shA with (hm_setn headamp_B_shA 48 13 ((-8) mod 256)) by (vm_compute; reflexivity).
  apply (hm_fsh_set rsegs (w_H W) memc (w_H W7) memD F headamp_B_shA 48 13 ((-8) mod 256) Hfsh).
  - intros j Hj. change (Z.of_nat 48) with 48 in Hj. change (Z.of_nat (48 + 13)) with 61 in Hj.
    rewrite KD by lia. apply Z4. lia.
  - intros j Hj Hn. rewrite LP0 in Hj. change (Z.of_nat 48) with 48 in Hn. change (Z.of_nat (48 + 13)) with 61 in Hn.
    rewrite KDC by lia. rewrite KC; [| lia | intros (_ & X); apply (SPP j); lia].
    apply K3A; [lia | intros X; apply (SFF j); lia | lia | intros X; apply (SPP j); lia | intros X; apply (SPP j); lia
               | lia]. }
split.
{ rewrite (HkD 5%bv) by hw5i_nc. rewrite (Hk4 5%bv) by hw5i_nc. rewrite C5.
  rewrite (hw5i_pres regsB regs3 18%bv HP3) by hw5i_cs. rewrite (HkB 18%bv) by hw5i_nc.
  rewrite (hw5i_pres regsA regsM 18%bv HPM) by hw5i_cs. rewrite A18. exact (G1 5%bv ltac:(vm_compute; lia)). }
split.
{ rewrite (HkD 13%bv) by hw5i_nc. rewrite (Hk4 13%bv) by hw5i_nc. rewrite C13.
  rewrite (hw5i_pres regsB regs3 23%bv HP3) by hw5i_cs. rewrite (HkB 23%bv) by hw5i_nc.
  rewrite (hw5i_pres regsA regsM 23%bv HPM) by hw5i_cs. rewrite A23. exact (G1 14%bv ltac:(vm_compute; lia)). }
split.
{ rewrite (HkD 17%bv) by hw5i_nc. rewrite (Hk4 17%bv) by hw5i_nc. rewrite C17.
  rewrite (hw5i_pres regsB regs3 21%bv HP3) by hw5i_cs. rewrite (HkB 21%bv) by hw5i_nc.
  rewrite (hw5i_pres regsA regsM 21%bv HPM) by hw5i_cs. rewrite A21. exact (G1 7%bv ltac:(vm_compute; lia)). }
split.
{ rewrite (HkD 28%bv) by hw5i_nc. rewrite (Hk4 28%bv) by hw5i_nc. rewrite C28.
  rewrite (hw5i_pres regsB regs3 20%bv HP3) by hw5i_cs. rewrite (HkB 20%bv) by hw5i_nc.
  rewrite (hw5i_pres regsA regsM 20%bv HPM) by hw5i_cs. rewrite A20. exact (G1 28%bv ltac:(vm_compute; lia)). }
rewrite (HkD 23%bv) by hw5i_nc. exact S7.
Qed.

(* ======================================== the piece ======================================== *)
(* a byte of pp's block outside the piece's write set: SPP keeps the frame's shadow granules apart from the block *)
Local Ltac hw5i_nE SPP y F :=
  unfold hw5i_E; let X := fresh "X" in intros X;
  destruct X as [X|[X|[X|[X|[? X]]]]];
  [ lia | apply (SPP (y - shadow_addr F)); lia | lia | lia | lia ].
Lemma hw5_piece_int : ameter_laws MT -> hsu_piece_W5_int_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using HW5_AMEMSET PWE.
intros MTL. unfold hsu_piece_W5_int_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hw5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof Hpre as (HJ0 & Hev & _ & H3 & H4 & _ & _ & _ & _ & Hown & HF & _).
cbn [hi_cid headamp_himg_B] in Hown, HF.
pose proof (@alloc_ceiling_value rc) as ([AC1 AC2] & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
assert (HFa : e_F (x_e cx) = frame_addr (x_ly cx) 4 (x_pos cx)) by (rewrite HF; exact (hw5i_fa 4 _ HJ0)).
unfold hsu_from_SELI. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselr).
destruct Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
unfold hsu_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (hw5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (hw5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
assert (A3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (hw5_getr5 regs2 3%bv 3 eq_refl). rewrite (Hr234 3 (or_intror (or_introl eq_refl))).
  rewrite (hw5_getr5 (x_regs cx) 3%bv 3 eq_refl). exact H3. }
assert (A4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (hw5_getr5 regs2 4%bv 4 eq_refl). rewrite (Hr234 4 (or_intror (or_intror eq_refl))).
  rewrite (hw5_getr5 (x_regs cx) 4%bv 4 eq_refl). exact H4. }
pose proof (hw5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hw5_in)) as A9.
pose proof (hw5_at_reg _ _ _ _ _ 19 (shadow_addr (e_F (x_e cx))) Hat ltac:(hw5_in)) as A19.
pose proof (hw5_at_reg _ _ _ _ _ 26 1 Hat ltac:(hw5_in)) as A26.
pose proof (hw5_at_reg _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hw5_in)) as A27.
pose proof (hw5_at_reg _ _ _ _ _ 5 (Z.of_nat (length ps)) Hat ltac:(hw5_in)) as A5.
pose proof (hw5_at_reg _ _ _ _ _ 14 (if sel mod 4 =? 0 then hsu_seen ps else 1) Hat ltac:(hw5_in)) as A14.
pose proof (hw5_at_reg _ _ _ _ _ 7 (hsu_cur rsegs cx rest r) Hat ltac:(hw5_in)) as A7.
pose proof (hw5_at_reg _ _ _ _ _ 28 (Z.of_nat (length r)) Hat ltac:(hw5_in)) as A28.
pose proof (hw5_at_cell _ _ _ _ _ 0x60 (e_F (x_e cx) + HSU_E42 + 0xc) Hat ltac:(hw5_in)) as V60.
pose proof (hw5_at_cell _ _ _ _ _ 0x68 (e_F (x_e cx) + HSU_E42) Hat ltac:(hw5_in)) as V68.
pose proof (hw5_at_cell _ _ _ _ _ 0x78 (e_pp (x_e cx) + Layout.OFF_HAS_PARAMS) Hat ltac:(hw5_in)) as V78.
pose proof (hw5_at_cell _ _ _ _ _ 0x140 (if sel mod 4 =? 0 then 0 else hsu_first ps) Hat ltac:(hw5_in)) as V140.
pose proof (hw5_at_cell _ _ _ _ _ 0x148 (e_pp (x_e cx)) Hat ltac:(hw5_in)) as V148.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen [c8 Hc8]].
assert (Hps2 : (length ps <= 2)%nat) by lia.
assert (Hat16 : 16 <= hsu_at_of sh ps) by (unfold hsu_at_of; pose proof (hw5_plen_lo sh ps Hsh7); lia).
assert (H5440 : hsu_at_of sh ps + 16 <= 5440) by (unfold hsu_at_of, hsu_plen; lia).
assert (Hmod8 : hsu_at_of sh ps mod 8 = 0).
{ replace (hsu_at_of sh ps) with ((c8 + 1) * 8) by (unfold hsu_at_of, hsu_plen; lia). apply Z_mod_mult. }
assert (Hfsv : hw5i_ifst sel ps = 0 \/ hw5i_ifst sel ps = 1).
{ unfold hw5i_ifst. destruct (sel mod 4 =? 0); [left; reflexivity | apply hw5_first_range]. }
change (if sel mod 4 =? 0 then 0 else hsu_first ps) with (hw5i_ifst sel ps) in V140.
unfold HSU_E42 in V60, V68.
rewrite Z.mod_small in V60 by lia. rewrite Z.mod_small in V68 by lia.
rewrite Z.mod_small in V78 by (unfold Layout.OFF_HAS_PARAMS; lia).
rewrite Z.mod_small in V140 by lia. rewrite Z.mod_small in V148 by lia.
pose proof (hw5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0)) = hsu_at_of sh ps).
{ rewrite !length_app, !length_le32. unfold hsu_at_of, hsu_plen. lia. }
assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
  (pp_image (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
  by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hsu_at_of sh ps)).
{ rewrite <- Hb0. refine (hm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
assert (Hfsh2 : hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) headamp_B_shA) by exact Hfsh.
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs (bi_SELI headamp_bld_B) regs2 mem2 md2) with (cfg_at rsegs 0x828ec regs2 mem2 md2).
  exact (hw5i_core (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps)
    (hw5i_ifst sel ps) (x_pos cx) MTL HJ Ppin2 Ppout Hev Hown HFa Hfsh2 A2 A3 A4 A9 A19 A26 A27
    V60 V68 V78 V140 V148 Vlen RB3 RB1 RB2 Hat16 H5440 Hmod8 Hfsv). }
intros W3 c3 _ Hpost.
assert (SHB : shadow_addr (e_F (x_e cx)) + 128 <= 17594332446848)
  by exact (proj2 (hw5i_sh_bounds (e_F (x_e cx)) ltac:(lia) ltac:(lia))).
assert (HEp : forall a, hw5i_E (e_F (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps) (hw5i_ifst sel ps) a ->
  hsu_E1 rsegs headamp_himg_B cx a).
{ intros a Ha. unfold hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
  destruct Ha as [X|[X|[X|[X|[_ X]]]]].
  - left. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
  - left. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
  - right. lia.
  - right. lia.
  - right. lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) hw5i_clob).
{ intros r0 [-> | [-> | ->]]; unfold hw5i_clob; hw5_notin. }
destruct (hw5_core_post B MT MTL cx (hsu_E1 rsegs headamp_himg_B cx) _ ly2 S2 W2 regs2 mem2 md2 0x82ae4 _ _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
  (Rbytes & Rlen & Rfl & Rfsh & R5 & R13 & R17 & R28 & R23)).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ hw5i_E (e_F (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps) (hw5i_ifst sel ps) a ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2. apply Hmem; [exact Ha | rewrite Hsp; exact H1 | exact H2]. }
assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x158 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; [lia | lia |]. unfold hw5i_E. intros X. lia. }
assert (HPF : e_pp (x_e cx) + 19744 <= e_F (x_e cx) \/ e_F (x_e cx) + 1024 <= e_pp (x_e cx)).
{ pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _).
  assert (HinF : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Hown).
  pose proof (sep_block_frame rsegs B (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ _ PP_SIZE 4 _ HAR0 Ppin HinF) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite <- HF in D.
  change (req_size PP_SIZE) with 19744 in D. change (fs_frame_bytes 4) with 1024 in D. exact D. }
assert (SPP : forall j, 0 <= j < 128 -> ~ (e_pp (x_e cx) <= shadow_addr (e_F (x_e cx)) + j < e_pp (x_e cx) + 19744)).
{ intros j Hj. apply (hw5i_sep_sh (e_F (x_e cx)) (e_pp (x_e cx)) 19744 j); [lia | lia | rewrite <- HPS; exact PApp | lia | exact Hj]. }
unfold hw5i_clob in Hkeep.
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x82ae4 regs3 mem3 md3) with (cfg_at rsegs (bi_LATCH headamp_bld_B) regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(hsu_key_of sel, PInt 7)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split; [exact Hcore3|].
split; [exact Rfsh|].
split.
{ unfold hsu_pp_at.
  change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(hsu_key_of sel, PInt 7)]) None))).
  rewrite (hw5i_img_int_eq sh ps sel Hsh7).
  assert (LI : length (enc_pod hw5i_e7) = 16%nat) by reflexivity.
  assert (Nb : hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx))
      ((pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) ++ enc_pod hw5i_e7)).
  { apply hm_bytes_app. split.
    - eapply hm_bytes_kept; [exact (hw5_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy. rewrite Hb0 in Hy.
      apply Kp; [lia | lia | hw5i_nE SPP y (e_F (x_e cx))].
    - rewrite Hb0. exact Rbytes. }
  apply (hw5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx))
    (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) _ _
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
  - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) (enc_pod hw5i_e7)). lia.
  - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) (enc_pod hw5i_e7)),
      Nat2Z.inj_add, Hb0, LI. unfold POD_BUF_MAX. lia.
  - exact EB1.
  - exact EB2.
  - rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) (enc_pod hw5i_e7)),
      Nat2Z.inj_add, Hb0, LI. exact Rlen.
  - destruct (Z.eqb_spec (hw5i_ifst sel ps) 1) as [E|E].
    + rewrite orb_true_r. exact (Rfl E).
    + rewrite orb_false_r.
      refine (proj1 (hw5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
      intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; [lia | lia |].
      hw5i_nE SPP y (e_F (x_e cx)).
  - eapply hm_bytes_kept.
    + apply hm_bytes_of_val. refine (hm_pp_params_struct rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia.
    + intros y Hy. rewrite ?length_le32, ?length_Z_to_le_bytes in Hy. unfold OFF_PARAMS_STRUCT in Hy.
      apply Kp; [lia | lia | hw5i_nE SPP y (e_F (x_e cx))].
  - intros y Hy. rewrite (length_app (pc_buf (PbCut sh ps None) ++ le32 (hsu_key_of sel) ++ le32 0) (enc_pod hw5i_e7)),
      Nat2Z.inj_add, Hb0, LI in Hy.
    unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
    apply Kp; [lia | lia | hw5i_nE SPP y (e_F (x_e cx))]. }
split; [exact Hin|]. split; [exact Hsuf|].
split; [apply hw5i_wf_int; [exact Hwf | exact Hps2]|].
split; [exact Hsh|]. split; [exact Hnp|].
split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
split; [exact (hw5i_loop_int sh ps sel rest r Hsh7 Hps Hselr Hsel4)|].
unfold hsu_at_cx, hsu_at.
rewrite (hw5i_seen_int ps sel).
replace (Z.of_nat (length (ps ++ [(hsu_key_of sel, PInt 7)])) - 1) with (Z.of_nat (length ps))
  by (rewrite length_app; cbn [length]; lia).
assert (L5 : hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (LReg 5) (Z.of_nat (length ps))).
{ cbn [hd_at]. rewrite (hw5_getr5 regs3 5%bv 5 eq_refl), R5, <- (hw5_getr5 regs2 5%bv 5 eq_refl). exact A5. }
assert (L13 : hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (LReg 13) (if sel mod 4 =? 0 then hsu_seen ps else 1)).
{ cbn [hd_at]. rewrite (hw5_getr5 regs3 13%bv 13 eq_refl), R13, <- (hw5_getr5 regs2 14%bv 14 eq_refl). exact A14. }
assert (L17 : hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (LReg 17) (hsu_cur rsegs cx rest r)).
{ cbn [hd_at]. rewrite (hw5_getr5 regs3 17%bv 17 eq_refl), R17, <- (hw5_getr5 regs2 7%bv 7 eq_refl). exact A7. }
assert (L28 : hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (LReg 28) (Z.of_nat (length r))).
{ cbn [hd_at]. rewrite (hw5_getr5 regs3 28%bv 28 eq_refl), R28, <- (hw5_getr5 regs2 28%bv 28 eq_refl). exact A28. }
assert (L23 : hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (LReg 23) (-8)).
{ cbn [hd_at]. rewrite (hw5_getr5 regs3 23%bv 23 eq_refl). exact R23. }
cbn [hsu_Rc1 hsu_Rc0 hsu_Kc app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
all: first [ exact L5 | exact L13 | exact L17 | exact L28 | exact L23 | hw5_kept Hat Hkeep Kc ].
Qed.
End c.

Print Assumptions hw5i_runA.
Print Assumptions hw5i_runB.
Print Assumptions hw5i_runC.
Print Assumptions hw5i_runD.
Print Assumptions hw5i_core.
Print Assumptions hw5_piece_int.
