(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_info (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8bb70, 122 instructions), after lib/A/Prog/answer_code.v (a working branch
   2ba4488ce71: a side-stack frame taken by __asan_stack_malloc_N, its header and shadow, the snprintf call and the
   release by the flag store) and lib/A/Prog/sup_instance_info.v (a working branch 0de7ca03d26: the
   recorder's chain through record, arg_s, rec_shape_of and answer and the post), re-derived on B's code, against
   a Theorem Labs lane's statement (a working branch f490061c104). The snprintf step through the shared contract and the change of FP
   state after it follow a working branch 07b554c4785 (lib/B/Prog/answer_code.v:943-1070), the release
   by the flag store answer_code.v's end, the post's block algebra a working branch b5e1a22725a
   (descriptors_panel_get_aux.v dpgb_post_of), the calls after record a working branch c79a9f2daf7. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_info.v, with its module paths and module names changed; 397 of its 567 lines of code are new or changed and 1652 lines of the source are left out. *)
(* The entry segment of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry BASE + AF_sup_host_setting = 0x8b53c), on the points and statements of sup_host_setting_s0.v:
   - hs_seg_entry: from the entry, the prologue (0x8b53c .. 0x8b580: the 160-byte frame, `sd zero,0(sp)`, the 13
     saves, s0 := sp0, the realignment `andi sp,sp,-32`, s1 := sp1), the GOT loads of the shadow base (A_OBJ 0 -> s10)
     and of the use-after-return flag (A_OBJ 1 -> the record's const cell, `lw a2` = 1), `beqz a2` (not taken), the
     call of __asan_stack_malloc_0 (0x8b5b0) through aj_stack_malloc_atS, the frame's slot, header and shadow
     (0x8b5b4 .. 0x8b644), and the call of record(6) (0x8a728, at 0x8b648) through cl_callS_wide, back at REC
     (0x8b64c), where the statement ST_REC takes over. The statement's premise hs_fxrel (i_fx x) fx (the owner's
     form since a Theorem Labs lane 713692f1e0c: the composition builds x with i_fx := fx) goes unchanged to
     ST_REC; __asan_stack_malloc_0 and record run at the Section's fx (hh_smalloc0 / hh_record taken at fx).
   Templates: the ASan walk of answer_code (A_answer_code.v: the side-stack frame's seed, run and keep facts), the B
   lane of sup_after_reply (B_sar_aux.v: the entry seed with the record's use-after-return const cell), and this
   walk's sup_host_setting_s3.v (a call through cl_callS_wide into a point's statement, read-only copy of the
   owner's file; its hs3_* helpers are used here).
   The use-after-return flag: `ld a2,-0x5e8(a2)` reads the GOT word A_OBJ 1 = as_got_uar B (palf_got_uar), which holds
   as_uar_cell B (al_const's fourth conjunct), and `lw a2,0(a2)` reads that cell, which holds 1 (al_const's second
   conjunct: lib/B/YF0m.v:88 `z4 (ANum 0xb0c40) 0x1` of the record's const cells). The seed carries both as region
   chunks (uar_got_regionP 33, uar_cell_regionP 33), so the executor reads a2 = 1 and decides `beqz a2` (0x8b5a8)
   not taken.
   The real-stack arm 0x8b5c8 .. 0x8b5e0 is not reached: s3 = the frame F that __asan_stack_malloc_0 returned; the
   state after the call carries the fact 4096 <= F (HPTR 6 on F's atom 1028, from frames_bounds), so the executor
   decides `bnez s3` (0x8b5c4) taken, to 0x8b5e4.
   No ASan report call and no UBSan trap site lies in 0x8b53c .. 0x8b648. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16 YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecAns CmdSnText RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


(* ---- arithmetic and denotation facts ---- *)
(* 0x8b53c `addi sp,sp,-160` .. 0x8b57c `andi sp,sp,-32`: the realigned sp *)
Lemma hs2_denot_and : forall E n v, ew E n = Z_to_bv 64 v -> 160 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n (-160)) (SLit (-32))) = Z_to_bv 64 (hs_sp1 v).
Proof.
intros E n v Hn Hv. unfold hs_sp1.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SOff n (-160)) (SLit (-32))))). f_equal.
change (U E (SAlu ALU_AND (SOff n (-160)) (SLit (-32))) = 32 * ((v - 160) / 32)).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + -160)) by lia.
replace (-32 mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite CmdSnText.snt_land_m32 by lia. replace (v + -160) with (v - 160) by lia.
pose proof (Z.div_pos (v - 160) 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (v - 160) 32 ltac:(lia)).
apply Z.mod_small. lia.
Qed.

Lemma hs2_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma hs2_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma hs2_nodup_disj : forall (l1 l2 : list (Z * Z)) y, List.NoDup (l1 ++ l2) -> In y l1 -> In y l2 -> False.
Proof.
induction l1 as [|z l1 IH]; intros l2 y ND H1 H2; [destruct H1|].
cbn [app] in ND. inversion ND as [|z' l' Hz ND' Heq]; subst.
destruct H1 as [<- | H1]; [apply Hz; apply in_or_app; right; exact H2 | exact (IH l2 y ND' H1 H2)].
Qed.

(* the stores of the prologue and of the frame setup: the zero word at sp0 - 160, the 13 saved registers at
   sp0 - 104 .. sp0, and the frame's slot at sp1 + 48 (0x8b5e4 `sd s4,0x30(s1)`); the GOT words and cells read *)
Definition hs2_extra (uar sp1 : Z) : list word := map (Z_to_bv 64) [HS_SB; uar; sp1].
Definition hs2_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-160) (-152) (-160) (-152) [];
 YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [];
 YP09.mkRegion (Some 34%nat) 48 56 48 56 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition hs2_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF HS_SB HS_SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_hs2 : sstate := mkSS AF_sup_host_setting sr_atoms hs2_regions0 None hs2_facts0.
(* the frame's header (F + 0 .. 24 written) and its shadow (8 bytes, all written) after the side-stack call *)
Definition hs2_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition hs2_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [].
Definition hs2_shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).
(* record()'s footprint (record_c.v), CmdRecAns.rca_recFP: g_rec.ncalls, the slot's fn and nargs, the spill's old
   argument blocks *)
Lemma hs2_FP1_cases : forall R O a, inFP (CmdRecAns.rca_recFP R O) a ->
  hs_in_rec a \/ (exists p n, In (p, n) O /\ p <= a < p + req_size n).
Proof.
intros R O a Ha. unfold CmdRecAns.rca_recFP in Ha. apply inFP_cons in Ha as [Ha | Ha].
- left. unfold hs_in_rec, A_G_REC, OFF_NCALLS, REC_SIZE in *. lia.
- apply inFP_cons in Ha as [Ha | Ha].
  + left. apply (hs3_slot_rec R a). unfold CALL_SIZE. lia.
  + right. destruct (Nat.ltb (length (r_calls R)) 16).
    * destruct Ha as (r & [] & _).
    * exact (inFP_ablocks_fp_inv O a Ha).
Qed.

(* a register's symbolic value, its denotation not normalised *)
Local Ltac hs2_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Local Ltac hs2_norm HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* an address outside every write window of a symbolic memory *)
Local Ltac hs2_nwin rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

Local Ltac hs2_in := repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma hs2_aval_of_val : forall H mem a n v, val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma hs2_region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma hs2_aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the frame after the prologue: the 13 saved registers, chunks of the stack region at sp0 - 104 .. sp0 *)
Lemma hs2_frame_of_region : forall E (m : word -> option byte) H sp0 regs cs,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 cs) ->
  bv_unsigned (ew E 2%nat) = sp0 ->
  (forall j r, nth_error HS_SAVED j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  hs_frame (aview SEGS H m) sp0 regs.
Proof.
intros E m H sp0 regs cs HR Hsp Hin HE j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold HS_SAVED in Hj. cbn [In] in Hj. lia. }
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
pose proof (field_of_region E _ 2 sp0 cs (-104) 0 (-104) 0 (-8 - 8 * Z.of_nat j) 8%N (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)) as V.
assert (V' : val_mem SEGS (mrestrict H m) (sp0 + (-8 - 8 * Z.of_nat j)) (N.to_nat 8) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ apply V; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].
  cbn [sv_denot]. rewrite (HE r Hr), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) in V' by lia.
exact (hs2_aval_of_val _ _ _ _ _ V').
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.

(* the entry's seed: the entry registers, the shadow base (32), the use-after-return cell (33), sp1 (34) *)
Lemma hs2_entry : forall W ly S regs mem md ch,
  afn_pre SEGS B SUP_HOST_SETTING_STK ly S W regs mem md ch ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (hs2_extra (as_uar_cell B) (hs_sp1 (spZ regs))))) ss_hs2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_host_setting)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof hs3_stk as FS.
pose proof (hh_TL B MT HH) as TL. pose proof (hh_TLF B MT HH) as TLF.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1.
pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
destruct (hs3_sp1 (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1b & Hsp1a).
set (sp1 := hs_sp1 (spZ regs)) in *.
set (E := Eimg (Ereg regs (hs2_extra (as_uar_cell B) sp1))).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 HS_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (HSBV : HS_SB = SHADOW_OFF) by (rewrite <- SB_SHADOW_OFF; reflexivity).
unfold ss_hs2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hs2_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [rewrite hs2_denot_off0; exact E253 | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) HS_SB);
    [rewrite hs2_denot_off0; exact E32 | unfold HS_SB; zside | zside |].
    rewrite Z.add_0_r, HSBV. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
    [rewrite hs2_denot_off0; exact E33 | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold hs2_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 Hstk0 HO0 HO1 HO12 Huar Hsep Hsp1 FS. clear. unfold ASAN_CEIL. intros.
  rewrite !Z.add_0_r in *. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat split; first [ assumption | (apply or_comm; assumption)
  | (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok hs2_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E34, !unsigned_lit_small by (unfold HS_SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  rewrite Hal16, Hsp1a. unfold HS_SB. repeat split; lia.
Qed.

(* ---- the entry: prologue, __asan_stack_malloc_0, the frame, record(6), back at REC ---- *)
Lemma hs_seg_entry : forall x, hs_cx B MT x -> hs_fxrel (i_fx x) fx -> ST_REC B MT x ->
  SRr SEGS (i_W x) (cfg_at SEGS (BASE + AF_sup_host_setting) (i_regs x) (i_mem x) (i_md x)) (hs_post B MT x).
Proof.
intros x CX FXR HREC.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMOK & HTAIL & HRM0).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (hh_TL B MT HH) as TL. pose proof (hh_TLF B MT HH) as TLF. pose proof (hh_HB B MT HH) as HB.
pose proof (hh_MTL B MT HH) as MTL. pose proof (hh_MTLF B MT HH) as MTLF.
pose proof hs3_stk as FS.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HRSV : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HPSB : as_prog_static B = recb_PG) by (rewrite (ts_prog B HB); reflexivity).
assert (HSBV : HS_SB = SHADOW_OFF) by (rewrite <- SB_SHADOW_OFF; reflexivity).
pose (ML := model_laws_ok (as_universe B) (ts_universe B HB)).
assert (SMP : stack_malloc_progressP B).
{ intros s cid HW Hc Hn. exact (stack_malloc_progress (as_universe B) s cid HW Hc Hn). }
assert (HOin : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (Hsp1 & Hsp1b & Hsp1a).
pose proof (hs2_entry (i_W x) (i_ly x) (i_S x) (i_regs x) (i_mem x) (i_md x) (i_ch x) HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_HOST_SETTING_STK (hs_FP (i_O x)) _ _ _ _ _ _ _ HPRE) as HJ.
remember (Eimg (Ereg (i_regs x) (hs2_extra (as_uar_cell B) (hs_sp1 (spZ (i_regs x)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (i_regs x) r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 HS_SB)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (i_regs x) _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (hs_sp1 (spZ (i_regs x))))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (i_regs x) _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ (i_regs x)))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ (i_regs x)) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = hs_sp1 (spZ (i_regs x))) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_sup_host_setting)) with (Z_to_bv 64 (BASE + AF_sup_host_setting)).
(* run 1: 0x8b53c .. 0x8b5b0, the prologue, the realignment, the GOT words, the use-after-return flag (1: `beqz a2`
   not taken), the call of __asan_stack_malloc_0 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_hs2, hs2_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := hs_sp1 (spZ (i_regs x)) - spZ (i_regs x));
    [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
  repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
hs2_preg HS (2%bv : bv 5) R2. hs2_preg HS (9%bv : bv 5) R9.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
rewrite (hs2_denot_and E 2 (spZ (i_regs x)) Esp ltac:(lia)) in R2.
rewrite hs2_denot_add0, (hs2_denot_and E 2 (spZ (i_regs x)) Esp ltac:(lia)) in R9.
rewrite (EE 3%nat 3%bv eq_refl) in R3. rewrite (EE 4%nat 4%bv eq_refl) in R4.
(* sp and s1 are sp1, atom 34 *)
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite hs2_denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite hs2_denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. hs2_norm HS.
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as SM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0.
rewrite SM0.
assert (Qsp : spZ (ms_regs ms1) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)))
  by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
(* the call of __asan_stack_malloc_0(64) at 0x8b5b0: the class-0 frame (0, fpos), owned by the call's journal *)
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 0 (hh_smalloc0 B MT HH fx) ltac:(lia)
    (i_W x) (ms_regs ms1) (ms_mem ms1) SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x)
    (i_mem x) (i_md x) [] (i_ly x) (i_S x) mdv1 0 (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (Z_to_bv 64 (BASE + 20612)) HJ);
  [ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | pose proof (count_cid_le_length 0 (frames (i_S x))); change (fs_frames 0) with 16384; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2
  & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H (i_W x)) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply hs2_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
  - eapply hs2_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
  - eapply hs2_region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R2 R9 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr (i_ly x) 0 fpos) in *. set (FL := flag_addr (i_ly x) 0 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (HS_SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (HS_SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (HS_SB + F / 8))
  by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (HS_SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 HS_SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ (i_regs x)) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = hs_sp1 (spZ (i_regs x))) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HFd8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HFm8.
assert (V1041 : bv_unsigned (ew E2 1041) = HS_SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold HS_SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 6) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 6) with 64; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv hs2_shx_F (SOff 1041 0) HS
  (shadow_decl_ok Ev 1028 32 1041 F HS_SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. hs2_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv hs2_fr_hdr HS eq_refl
  ltac:(unfold region_ok, hs2_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, hs2_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. hs2_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv hs2_fr_shd HS eq_refl
  ltac:(unfold region_ok, hs2_fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite V1041; split; [unfold HS_SB; lia|]; split; [unfold HS_SB; lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS);
    replace (HS_SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- HSBV; lia);
    apply (proj1 (HFSpres o ltac:(lia))))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, hs2_fr_shd, hs2_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite V1041, V1028, V2, V34; unfold HS_SB; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. hs2_norm HS.
(* run 2: 0x8b5b4 .. 0x8b648, s3 := s4 := F, `bnez s3` taken (4096 <= F: the real-stack arm 0x8b5c8 .. 0x8b5e0 is not
   reached), the frame's slot at sp1 + 48, its header (magic 0x41b58ab3, A_OBJ 59, A_OBJ 62), its shadow
   (f1 f1 f1 f1 f8 f8 f3 f3), a0 := 6, the call of record *)
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- HSBV; change (fs_frame_bytes 0 / 8) with 8; lia |].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := hs_sp1 (spZ (i_regs x)) - spZ (i_regs x));
    [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
(* the registers at the call of record *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (18%bv : bv 5) P18.
prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
rewrite OLD2, E34 in P2 by lia. rewrite OLD2, E34 in P9 by lia. rewrite OLD2, Esp in P8 by lia.
rewrite OLD2, (EE 3%nat 3%bv eq_refl) in P3 by lia. rewrite OLD2, (EE 4%nat 4%bv eq_refl) in P4 by lia.
rewrite E2028 in P19. rewrite E2028 in P20. rewrite V1028 in P23.
rewrite OLD2, (EE 12%nat 12%bv eq_refl), H12 in P21 by lia. rewrite OLD2, (EE 10%nat 10%bv eq_refl), H10 in P22 by lia.
rewrite OLD2, (EE 11%nat 11%bv eq_refl), H11 in P24 by lia. rewrite E1041 in P25. rewrite E2_32 in P26.
assert (P18' : getr (ms_regs ms3) 18 = w64 (-8)).
{ rewrite P18. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
clear P18.
assert (Qsp3 : spZ (ms_regs ms3) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2, unsigned_lit_small by lia. lia. }
assert (SIGR : SIG CS_record = BASE + AF_record).
{ rewrite (hh_sigp B MT HH CS_record ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
rewrite SIGR.
(* where the recorder's state lies: g_rec, record.spill and the recorder's blocks O; none in the frame or its
   shadow, all below the allocator's ceiling *)
set (KA := fun a : Z => hs_in_rec a \/ (exists p n, In (p, n) (i_O x) /\ p <= a < p + req_size n)).
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (HS_SB + F / 8 <= a < HS_SB + F / 8 + 8)).
{ intros a [Ha | (p & n & Hpn & Ha)].
  - assert (Himg : in_img SEGS a) by exact (hh_prog_img B MT HH a (proj2 (hs3_rec_fp (i_O x) a Ha))).
    assert (Hab : 6173376 <= a < 6174616) by (unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    split; [lia|]. split.
    + intros HFa. exact (frm_img SEGS B LAWS (i_ly x) S2 (i_W x) mem2 md2 0 fpos a HAR2 Hfin
        ltac:(fold F; change (fs_frame_bytes 0) with 64; lia) Himg).
    + unfold HS_SB. lia.
  - pose proof (HOin (p, n) Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn).
    assert (Hin2 : In (p, n) (ablocks B (i_ly x) S2)) by (rewrite Eab; exact Hin).
    pose proof (sep_block_frame SEGS B LAWS (i_ly x) S2 (i_W x) mem2 md2 p n 0 fpos HAR2 Hin2 Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    split; [lia|]. split; [lia|]. unfold HS_SB. lia. }
assert (K01 : forall a, KA a -> aview SEGS (w_H (i_W x)) (ms_mem ms1) a = aview SEGS (w_H (i_W x)) (i_mem x) a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _).
  apply (hs2_aview_frame_pt E _ (w_H (i_W x)) (i_mem x) (ms_mem ms1) a HFr1); [lia|].
  hs2_nwin ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H (i_W x)) mem2 a = aview SEGS (w_H (i_W x)) (ms_mem ms1) a).
{ intros a [Ha | (p & n & Hpn & Ha)].
  - destruct (hs3_rec_fp (i_O x) a Ha) as [_ Hpg].
    assert (Hpg' : Exists (in_zr a) (as_prog_static B)) by (rewrite HPSB; exact Hpg).
    destruct (prog_static_sep B a (ts_ok B HB) Hpg') as (Hno & Hne & _).
    exact (HK3 a (hh_prog_img B MT HH a Hpg) Hno Hne).
  - replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) (HOin _ Hpn)); [lia | intros []]. }
assert (K23 : forall a, KA a -> aview SEGS (w_H (i_W x)) (ms_mem ms3) a = aview SEGS (w_H (i_W x)) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS).
  apply (hs2_aview_frame_pt E2 _ (w_H (i_W x)) mem2 (ms_mem ms3) a HFr3); [lia|].
  hs2_nwin ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H (i_W x)) (ms_mem ms3) a = aview SEGS (w_H (i_W x)) (i_mem x) a)
  by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha); exact (K01 a Ha)).
assert (FPKA : forall a, inFP (CmdRecAns.rca_recFP (i_R x) (i_O x)) a -> KA a) by (intros a Ha; exact (hs2_FP1_cases _ _ a Ha)).
(* the frame's flag pointer at F + 56 (__asan_stack_malloc_0's post), kept by run 2 *)
assert (HFL3 : aval_mem (rdW (i_W x) (ms_mem ms3)) (F + 56) 8 FL).
{ apply (hs3_aval_on (rdW (i_W x) mem2)); [| exact (hs2_aval_of_val _ _ _ _ _ (val_mem_of_rdword SEGS (w_H (i_W x)) mem2 _ _ Hflag))].
  intros b Hb. change (Z.of_nat 8) with 8 in Hb.
  apply (hs2_aview_frame_pt E2 _ (w_H (i_W x)) mem2 (ms_mem ms3) b HFr3); [lia|].
  hs2_nwin ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; unfold HS_SB in *; lia). }
(* the 13 saved registers, the chunks of the stack region at sp0 - 104 .. sp0 *)
pose proof (st_ok_region_nth E2 _ _ 3 _ HS eq_refl) as HRG. cbn [ms_mem restrict mkst] in HRG.
assert (HFRc : hs_frame (rdW (i_W x) (ms_mem ms3)) (spZ (i_regs x)) (i_regs x)).
{ apply (hs2_frame_of_region E2 (ms_mem ms3) (w_H (i_W x)) (spZ (i_regs x)) (i_regs x) _ HRG V2).
  - intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; hs2_in|]).
    destruct j; cbn in Hj; discriminate Hj.
  - intros r Hr. rewrite OLD2 by lia. apply EE. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
(* record's premises at the call *)
destruct (hs3_rod_now B MT HH x fpos (i_ly x) S2 (i_W x) (ms_mem ms3) mdv 0 CX HJ2) as [HRODc HROc].
destruct (hs3_achain B MT x fpos (i_ly x) S2 (i_W x) (ms_mem ms3) mdv 0 (ms_regs ms3) CX HJ2 HFRc ltac:(rewrite Qsp3; lia) P8)
  as (ch1 & HCH).
assert (KOWN : forall a, hs_in_rec a \/ hs_in_own (i_O x) a -> KA a).
{ intros a [Ha | ((p, n) & Hpn & Ha)]; [left; exact Ha | right; exists p, n; split; [exact Hpn|]].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. cbn [fst snd] in Ha. lia. }
assert (REPc : rec_repA B (i_ly x) S2 (rdW (i_W x) (ms_mem ms3)) (i_R x) (i_O x)).
{ apply (hs_rec_kept B (i_ly x) (i_S x) (i_ly x) S2 (rdW (i_W x) (i_mem x)) (rdW (i_W x) (ms_mem ms3)) (i_R x) (i_O x) HREP0).
  - intros a Ha. exact (K03 a (KOWN a Ha)).
  - intros pn Hpn. rewrite Eab. exact (HOin pn Hpn). }
assert (HEVc : st_nev S2 + EV_RECORD (i_R x) <= EV_MAX).
{ rewrite Hnev2. unfold EV_SUP_HOST_SETTING in HEV. unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC in HEV. lia. }
assert (HMOc : mo_ok MT S2 (XM_RECORD MT (i_R x))).
{ rewrite ES2. apply (mo_ok_set_fs MT MTLF).
  apply (mo_ok_le MT MTL _ _ (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x))); [exact HMOK|].
  unfold XM_SUP_HOST_SETTING.
  pose proof (hs3_xl_nonneg B MT HH (i_line x)).
  pose proof (hs3_xs_nonneg B MT HH (Some (dec (Z.of_nat (length (i_toks x)))))).
  pose proof (hs3_xs_nonneg B MT HH (Some (join_sp (i_toks x)))).
  pose proof (hs3_xx_nonneg B MT HH (hs_words_len (i_toks x) + 1)).
  pose proof (mo_free_nonneg MT MTL). lia. }
(* the call of record(6) at 0x8b648 *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS (i_W x) (ms_regs ms3) (ms_mem ms3) (Z_to_bv 64 (BASE + AF_record)) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] (i_ly x) S2 mdv 0
    RECORD_STK (CmdRecAns.rca_recFP (i_R x) (i_O x)) (EV_RECORD (i_R x)) (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))
    (getr (ms_regs ms3) 1) ch1 _ HJ2 Qsp3 Hsp1b ltac:(lia) ltac:(rewrite HRSV; lia) ltac:(rewrite HRSV, FS; lia)).
  - rewrite P3. exact Hgp.
  - rewrite P4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - replace (spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))) with (spZ (ms_regs ms3)) by lia. exact HCH.
  - intros HPRE1.
    exact (hh_record B MT HH fx (i_ly x) S2 (i_W x) (ms_regs ms3) (ms_mem ms3) mdv ch1 REC_HOST_SETTING (i_R x) (i_O x)
      HPRE1 HRODc P10 ltac:(change REC_HOST_SETTING with 6; change REC_FN_COUNT with 26; lia) REPc HEVc HMOc).
  - intros a Ha. destruct (hs2_FP1_cases (i_R x) (i_O x) a Ha) as [Hr | (p & n & Hpn & Hpa)].
    + right; right; right; right; left. destruct (hs3_rec_fp (i_O x) a Hr) as [Hfp Hpg].
      split; [exact Hfp|]. split; [rewrite HPSB; exact Hpg | exact (hh_prog_img B MT HH a Hpg)].
    + right; left. split.
      * exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
        right; right. unfold ablocks_fp. exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ _ Hpn).
      * exists p, n. split; [rewrite Eab; exact (HOin _ Hpn) | exact Hpa].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    destruct (KLOC a (FPKA a Ha)) as (Hb & _). rewrite FS in Hw. lia. }
(* back at REC 0x8b64c *)
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJ3c & HP3 & HKr).
destruct HKr as (FR & O' & Ra0 & HPERM & HFRlen & HFRO & HREP3 & HO' & HBB3 & HMLE3).
pose proof HJ3c as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
rewrite P1.
refine (HREC fpos ly3 S3 W3 mem3 md3 regs3 (0 + EV_RECORD (i_R x)) O' (ablocks B ly3 S3) CX FXR _ _ _ Ra0).
- refine (conj HJ3 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  + unfold hs_k0, EV_RECORD. rewrite <- HFRlen. lia.
  + unfold hs_m0. apply (mo_le_set_fs_l MT MTLF (i_S x) S3 fS2). rewrite <- ES2. exact HMLE3.
  + lia.
  + apply (hs3_frame_kept_on (rdW (i_W x) (ms_mem ms3))); [|exact HFRc].
    intros b Hb. apply J1; [lia | rewrite HRSV; lia |].
    intros Hin. destruct (KLOC b (FPKA b Hin)) as (Hb2 & _). lia.
  + change (hs_F x fpos) with F. change (hs_FL x fpos) with FL.
    apply (hs3_aval_on (rdW (i_W x) (ms_mem ms3))); [|exact HFL3].
    intros b Hb. change (Z.of_nat 8) with 8 in Hb. apply (J4 0 fpos b Hfin).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 0) with 64. lia.
    * intros Hin. destruct (KLOC b (FPKA b Hin)) as (_ & HnF & _). lia.
  + pose proof (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR2) as ND. rewrite Eab in ND. rewrite Eab in HPERM.
    pose proof (Permutation_NoDup HPERM ND) as ND3.
    split; [apply Permutation_refl|].
    split; [intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn|].
    split.
    { intros pn Hpn Hno. apply (Permutation_in _ HPERM) in Hpn. apply in_app_or in Hpn as [Hp | Hp]; [exact Hp|].
      exfalso. exact (Hno (HFRO pn Hp)). }
    split.
    { intros pn Hpn HpO. apply HO'. split; [exact HpO|]. intros HpF. exact (hs2_nodup_disj _ _ pn ND3 Hpn HpF). }
    split; [intros pn Hpn; exact (proj1 (proj1 (HO' pn) Hpn))|].
    split; [intros pn []|].
    intros pn Hpn. destruct (proj1 (HO' pn) Hpn) as [HpO HnF].
    pose proof (HOin pn HpO) as Hin. apply (Permutation_in _ HPERM) in Hin.
    apply in_app_or in Hin as [Hp | Hp]; [exact Hp | exfalso; exact (HnF Hp)].
- exact HREP3.
- split.
  + split; [transitivity (getr (ms_regs ms3) 2); [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms3) 9); [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms3) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms3) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms3) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms3) 24); [exact (HP3 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms3) 25); [exact (HP3 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms3) 26); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms3) 18); [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact P18']|].
    split; [transitivity (getr (ms_regs ms3) 19); [exact (HP3 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms3) 20); [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    split; [transitivity (getr (ms_regs ms3) 21); [exact (HP3 21 ltac:(unfold acallee_saved; lia)) | exact P21]|].
    split; [transitivity (getr (ms_regs ms3) 22); [exact (HP3 22 ltac:(unfold acallee_saved; lia)) | exact P22]|].
    transitivity (getr (ms_regs ms3) 23); [exact (HP3 23 ltac:(unfold acallee_saved; lia)) | exact P23].
Qed.

End e.
End f.
End d.
