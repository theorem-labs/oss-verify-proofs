(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the code-level part of sup_policy_set's walk on the ASan+UBSan build of
   plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x8be08, 28 instructions, BASE + AF_sup_policy_set),
   which depends on no callee contract: the call targets, the verb literal, the frame, and the five straight-line
   runs between the program calls (entry to record, record to arg_s, arg_s to arg_s, arg_s to rec_shape_of,
   rec_shape_of to the tail jump into answer), each stated for any continuation. The B re-walk of
   lib/A/Prog/sup_policy_set_s1.v / _s2.v (a working branch 02d1c730d1b), whose code inlines record() and
   xstrdup; B calls record() and arg_s() instead (lib/B/Prog/sup_policy_set_c.v on a working branch fc8bcbd8b42;
   record's call target is CmdRecAns.v's rca_sig_record).
   The B code has no inline ASan check and no UBSan trap site, so no run below meets a report or trap edge.
   Measured on fuzz_command.asan-ubsan (sha256 658cefbe...), .symtab sup_policy_set 0x8be08 size 0x70:
     0x8be08 addi sp,sp,-32 / sd ra,24(sp) / sd s0,16(sp) / sd s1,8(sp) / sd s2,0(sp) / mv s0,a1 / mv s1,a0 /
     li a0,12 / 0x8be28 jal record (0x8a728) / 0x8be2c mv s2,a0 / mv a1,s1 / 0x8be34 jal arg_s (0x8a820) /
     0x8be38 mv a0,s2 / mv a1,s0 / 0x8be40 jal arg_s / 0x8be44 auipc a0 / addi a0 (= 0x21e80, "policy_set") /
     li a1,10 / 0x8be50 jal rec_shape_of (0x896d4) / 0x8be54 li a2,1 / mv a1,a0 / mv a0,s2 / ld ra,24(sp) /
     ld s0,16(sp) / ld s1,8(sp) / ld s2,0(sp) / addi sp,sp,32 / 0x8be74 j answer (0x8aa10).
   Listing lines: lib/B/Prog/CmdList.v:5765-5792 (slot 5686 = 0x58d8 / 4); the auipc pair is
   `PHi a0 168; PAddHi a0 a0 168 (A_OBJ 71) 0`, an address formation (no load or store through an A_HI base). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaLibF PaLibG PaLibH PaSB
PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the function's cut points (MEASURED, see the header) -------------------------------------------------- *)
Definition SPS_ENTRY : Z := AF_sup_policy_set.           (* 0x8be08 *)
Definition SPS_FRAME : Z := 32.
Definition SPS_RET_REC : Z := AF_sup_policy_set + 0x24.  (* 0x8be2c, after record(12) *)
Definition SPS_RET_A1 : Z := AF_sup_policy_set + 0x30.   (* 0x8be38, after arg_s(slot, format) *)
Definition SPS_RET_A2 : Z := AF_sup_policy_set + 0x3c.   (* 0x8be44, after arg_s(slot, place) *)
Definition SPS_RET_RSO : Z := AF_sup_policy_set + 0x4c.  (* 0x8be54, after rec_shape_of("policy_set", 10) *)
(* the verb literal rec_shape_of is given (CmdRo.v RO_lit_21e80) *)
Definition SPS_NAME : Z := 0x21e80.
Definition sps_verb : list byte := bstr "policy_set".
Definition sps_shape : list byte := daemon_shape "policy_set".
(* the registers the prologue saves, in the order of their slots below the entry sp: ra at sp0 - 8, s0 at
   sp0 - 16, s1 at sp0 - 24, s2 at sp0 - 32 *)
Definition sps_saved : list Z := [1; 8; 9; 18].
Definition sps_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sps_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the registers each run leaves as they were *)
Definition sps_kept_pro : list Z := [3; 4; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sps_kept_mid1 : list Z := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sps_kept_mid : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sps_kept_epi : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* --- the symbolic states the runs start from ----------------------------------------------------------- *)
(* atom 2 is the sp of the state; the entry state has the 32-byte frame below it, writable; the last state has the
   frame above it, read-only, holding the entry values of ra, s0, s1, s2 as atoms 32 .. 35 *)
Definition sps_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_spsA : sstate := mkSS SPS_ENTRY sr_atoms [stack_region SPS_FRAME] None sps_facts.
Definition sps_extraT (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) sps_saved.
Definition sps_stackT : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition ss_spsT : sstate := mkSS SPS_RET_RSO sr_atoms [sps_stackT] None sps_facts.
(* no shadow entry: the function has no inline check *)
Definition sps_Bx : sv := SOff 32 0.
Definition sps_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
(* the chunks the prologue stores, below atom 2 *)
Definition sps_fchunks : list YP09.chunk :=
[YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma sps_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the reader facts a callee is given, carried across a run that keeps every byte *)
Lemma sps_abytes_kept : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l K H i Hi. rewrite K. exact (H i Hi). Qed.
Lemma sps_ro_ok_kept : forall (rd rd' : reader), (forall x, rd' x = rd x) -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' K [HB HT]. split.
- unfold cmd_ro_bytes in *.
  repeat match goal with H : _ /\ _ |- _ /\ _ =>
    let H1 := fresh "H1" in destruct H as [H1 H]; split; [exact (sps_abytes_kept rd rd' _ _ K H1) |] end.
  exact (sps_abytes_kept rd rd' _ _ K HB).
- intros e He a Ha. rewrite K. exact (HT e He a Ha).
Qed.
Lemma sps_aro_kept : forall segs rlo rhi B (rd rd' : reader), (forall x, rd' x = rd x) ->
arodata_okP segs rlo rhi B rd -> arodata_okP segs rlo rhi B rd'.
Proof. intros segs rlo rhi B rd rd' K H a H1 H2 H3. rewrite K. exact (H a H1 H2 H3). Qed.
(* the registers the middle runs keep are callee-saved, so every callee keeps them too *)
Lemma sps_kept_mid_saved : forall r, In r sps_kept_mid -> acallee_saved r.
Proof.
intros r Hr. cbv [sps_kept_mid In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr]; [lia|]). destruct Hr.
Qed.
(* a byte range none of a concrete list of ranges holds *)
Lemma sps_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma sps_abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by lia. exact H.
Qed.
(* the conjunct of a long conjunction that is the goal *)
Ltac sps_proj H :=
  lazymatch type of H with
  | _ /\ _ => first [exact (proj1 H) | let H2 := constr:(proj2 H) in sps_proj H2]
  | _ => exact H
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma sps_kept_all : forall H (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' K a.
assert (Hz : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
pose proof (K (a mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as Ka. unfold aview, mbyte in *. rewrite Hz. exact Ka.
Qed.

Lemma sps_aval_val : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hv. unfold aview in Hv.
unfold val_mem.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hv. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

Lemma sps_val_aval : forall (W : world SEGS) mem a n v,
val_mem SEGS (mrestrict (w_H W) mem) a n v -> aval_mem (rdW W mem) a n v.
Proof.
intros W mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the frame the prologue stores, read back from any region at atom 2 that holds sps_fchunks *)
Lemma sps_frame_of_region : forall E (W : world SEGS) m sp0 (regs : bvmap 5 word) lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
incl sps_fchunks cs ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
sps_frame (rdW W m) sp0 regs.
Proof.
intros E W m sp0 regs lo hi wlo whi cs HR Hinc Hsp Hew j r Hj.
assert (Hj4 : (j < 4)%nat) by (apply (proj1 (nth_error_Some sps_saved j)); rewrite Hj; discriminate).
apply sps_val_aval.
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
assert (ONE : forall off rn, In (YP09.mkChunk off (CVal 8 (SOff rn 0))) sps_fchunks -> Z.of_nat rn = r -> (rn < 32)%nat ->
  val_mem SEGS (mrestrict (w_H W) m) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off rn Hin Hrn Hrn32. change 8%nat with (N.to_nat 8).
  apply (field_of_region E _ 2 sp0 cs lo hi wlo whi off 8 (SOff rn 0) _ HR Hsp (Hinc _ Hin)); [| exact HRr | cbn; lia].
  rewrite sps_soff0. rewrite (Hew rn (Z_to_bv 5 r)); [symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrn. }
do 4 (destruct j as [|j]; [cbn [nth_error sps_saved] in Hj; injection Hj as <-;
  match goal with |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?jj) _ _ =>
    let off := eval cbv in (-8 - 8 * Z.of_nat jj) in
    replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + off) by (cbn; lia) end;
  (eapply ONE; [cbn [sps_fchunks In]; tauto | reflexivity | lia]) |]).
lia.
Qed.

(* the trivial seed: the registers as atoms, no region *)
Lemma sps_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sps_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* the seed of the entry run: the 32-byte frame below the entry sp is present, so writable *)
Lemma sps_seedA : forall (W : world SEGS) (regs : bvmap 5 word) mem STK,
SPS_FRAME <= STK -> 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_spsA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SPS_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sps_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem STK HSTK Hsp Hal Hpres.
set (E := Eimg (Ereg regs [])).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
split; [|apply Forall_nil].
unfold ss_spsA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold stack_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E2. unfold SPS_FRAME in *. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + constructor.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; exact I].
  cbn [sps_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact Hal | lia].
Qed.

(* the seed of the last run: the frame above atom 2 holds the entry values of ra, s0, s1, s2 *)
Lemma sps_seedT : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem sp0,
spZ regs = sp0 - SPS_FRAME -> 2 ^ 46 <= sp0 - SPS_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
sps_frame (rdW W mem) sp0 regs0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sps_extraT regs0))) ss_spsT
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SPS_RET_RSO)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sps_Bx [] (Eimg (Ereg regs (sps_extraT regs0))) (mrestrict (w_H W) mem).
Proof.
intros W regs regs0 mem sp0 Hsp Hlo Hhi Hal HFR.
set (E := Eimg (Ereg regs (sps_extraT regs0))).
assert (E2 : bv_unsigned (ew E 2) = sp0 - SPS_FRAME).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). exact Hsp. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (sps_extraT regs0) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
split; [|apply Forall_nil].
unfold ss_spsT. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold sps_stackT, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E2. unfold SPS_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?m 0))) =>
    let j := eval compute in (m - 32)%nat in
    let r := eval compute in (nth j sps_saved 0) in
    apply (chunk_ok_val SEGS E _ (sp0 - 32) off 8 (SOff m 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
    [ rewrite sps_soff0; change m with (32 + j)%nat; rewrite EX by lia; cbn [nth sps_extraT map sps_saved];
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HR
    | cbn; lia
    | apply sps_aval_val;
      replace (sp0 - 32 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
      exact (HFR j r eq_refl) ]
  end.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; exact I].
  cbn [sps_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. unfold SPS_FRAME in *. split; [|exact I]. split; [lia|]. split; [|lia].
  Z.div_mod_to_equations. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
(* the bridge from the listing's object atoms to the image's addresses (the statement's own VOBJS) *)
Hypothesis VOBJS : cmd_val_objs.
(* the call target of every program function (CmdObj.v's cmd_sig_prog), the named record fact the A walk takes *)
Hypothesis SIGP : cmd_sig_prog.

Lemma sps_sig : forall s, In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. intros s Hs. exact (SIGP s Hs). Qed.
Ltac sps_in_syms := cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]).
Lemma sps_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite sps_sig by sps_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma sps_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite sps_sig by sps_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma sps_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite sps_sig by sps_in_syms. f_equal; try (vm_compute; reflexivity). Qed.

(* the verb literal: the listing's atom A_OBJ 71 is 0x21e80, and its bytes are "policy_set" *)
Lemma sps_name_val : VAL (A_OBJ 71) = SPS_NAME.
Proof. rewrite (VOBJS 71%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sps_verb_lit : RO_lit_21e80 = sps_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Ltac sps_pc_to t :=
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
    replace p with t by (rewrite ?(rca_sig_record SIGP), ?sps_sig_arg_s, ?sps_sig_rec_shape_of, ?sps_sig_answer;
                         cbv [AF_record AF_arg_s AF_rec_shape_of AF_answer]; lia) end.

Ltac sps_kept HS HAE l :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  first [ apply (regs_kept_of_st_ok_pi _ _ _ _ _ (map (Z_to_bv 5) l) HS HAE ltac:(vm_compute; reflexivity))
        | apply (regs_kept_of_st_ok SEGS _ _ _ _ _ (map (Z_to_bv 5) l) HS HAE ltac:(vm_compute; reflexivity)) ];
  apply in_map; exact Hr.

Ltac sps_keep_all :=
  apply sps_kept_all; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr); [| exact Ha | tauto] end;
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]); destruct Hin.

Ltac sps_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ssx (restrict ?H ?msx) =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem restrict mkst] in HR
  | st_ok _ ?E ?ssx (restrict ?H ?msx) =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem restrict mkst] in HR
  end.

Ltac sps_awr_lit :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.

(* --- the entry: the prologue and the call of record(12) (0x8be08 .. 0x8be28) -------------------------------- *)
Lemma sps_pro : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch STK FP Q,
afn_pre SEGS B STK ly S W regs mem md ch -> SPS_FRAME <= STK ->
(forall (regs1 : bvmap 5 word) mem1 md1,
  ajournal SEGS B STK (spZ regs) FP ly S W mem md [] ly S W mem1 md1 0 ->
  getr regs1 1 = Z_to_bv 64 (BASE + SPS_RET_REC) ->
  getr regs1 2 = w64 (spZ regs - SPS_FRAME) ->
  getr regs1 8 = getr regs 11 -> getr regs1 9 = getr regs 10 -> getr regs1 10 = w64 REC_POLICY_SET ->
  (forall r, In r sps_kept_pro -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  sps_frame (rdW W mem1) (spZ regs) regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SPS_FRAME <= a < spZ regs) -> rdW W mem1 a = rdW W mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_record) regs1 mem1 md1) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_ENTRY) regs mem md) Q.
Proof.
intros ly S W regs mem md ch STK FP Q HPRE HSTK K.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp' : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold SPS_FRAME in HSTK; lia).
destruct (sps_seedA W regs mem STK HSTK Hsp' Hal16 Hpres) as [HS SHOK].
pose proof (ajournal_init SEGS B STK FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs [])) m = getr regs rr)
  by (intros m rr Hm; apply ew_Eimg_Ereg_nat; exact Hm).
assert (HAE : env_agree 32 (Ereg regs []) (Eimg (Ereg regs []))).
{ split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at, w64. unfold SPS_ENTRY in HS |- *.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; unfold SPS_FRAME in HSTK; lia | cbn; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10.
sps_pc_to (BASE + AF_record).
unfold cfg_at, w64 in K.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ mem) (mrestrict _ ?m1) |- _ =>
  rename Hfr into HFrA end.
lazymatch goal with Hg : mem_grows (mrestrict _ mem) (mrestrict _ ?m1) |- _ => rename Hg into HGA end.
apply K.
- exact HJ.
- rewrite Q1. unfold SPS_RET_REC, AF_sup_policy_set. reflexivity.
- rewrite Q2, Usp; unfold w64, SPS_FRAME; f_equal; lia.
- rewrite Q8. apply EEo. reflexivity.
- rewrite Q9. apply EEo. reflexivity.
- rewrite Q10. reflexivity.
- sps_kept HS HAE sps_kept_pro.
- sps_region HS 0%nat HRs.
  eapply (sps_frame_of_region E W _ (spZ regs) regs _ _ _ _ _ HRs); [| exact Usp | exact EEo].
  intros c Hc. cbn [sps_fchunks In] in Hc. cbn [In].
  repeat (destruct Hc as [<- | Hc]; [tauto|]). destruct Hc.
- intros a Ha Hnot.
  apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem _ (fun a => spZ regs - SPS_FRAME <= a < spZ regs) HFrA);
  [| exact Ha | exact Hnot].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite Usp in Hrr.
  unfold SPS_FRAME. lia.
- exact HGA.
Qed.

(* --- record's return to the call of arg_s on format (0x8be2c .. 0x8be34): s2 := a0 (the slot), a1 := s1 ------- *)
Lemma sps_mid1 : forall (W : world SEGS) (regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall (regs1 : bvmap 5 word) mem1 md1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, rdW W mem1 a = rdW W mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
  getr regs1 1 = Z_to_bv 64 (BASE + SPS_RET_A1) ->
  getr regs1 18 = getr regs 10 -> getr regs1 10 = getr regs 10 -> getr regs1 11 = getr regs 9 ->
  (forall r, In r sps_kept_mid1 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_arg_s) regs1 mem1 md1) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_RET_REC) regs mem md) Q.
Proof.
intros W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ K.
destruct (sps_seed0 W regs mem SPS_RET_REC) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs [])) m = getr regs rr)
  by (intros m rr Hm; apply ew_Eimg_Ereg_nat; exact Hm).
assert (HAE : env_agree 32 (Ereg regs []) (Eimg (Ereg regs []))).
{ split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (18%bv : bv 5) Q18.
sps_pc_to (BASE + AF_arg_s).
unfold cfg_at, w64 in K.
lazymatch goal with Hg : mem_grows (mrestrict _ mem) (mrestrict _ ?m1) |- _ => rename Hg into HGA end.
apply K.
- exact HJ.
- sps_keep_all.
- exact HGA.
- rewrite Q1. unfold SPS_RET_A1, AF_sup_policy_set. reflexivity.
- rewrite Q18. apply EEo. reflexivity.
- rewrite Q10. apply EEo. reflexivity.
- rewrite Q11. apply EEo. reflexivity.
- sps_kept HS HAE sps_kept_mid1.
Qed.

(* --- arg_s's return to the call of arg_s on place (0x8be38 .. 0x8be40): a0 := s2, a1 := s0 ------------------- *)
Lemma sps_mid2 : forall (W : world SEGS) (regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall (regs1 : bvmap 5 word) mem1 md1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, rdW W mem1 a = rdW W mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
  getr regs1 1 = Z_to_bv 64 (BASE + SPS_RET_A2) ->
  getr regs1 10 = getr regs 18 -> getr regs1 11 = getr regs 8 ->
  (forall r, In r sps_kept_mid -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_arg_s) regs1 mem1 md1) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_RET_A1) regs mem md) Q.
Proof.
intros W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ K.
destruct (sps_seed0 W regs mem SPS_RET_A1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs [])) m = getr regs rr)
  by (intros m rr Hm; apply ew_Eimg_Ereg_nat; exact Hm).
assert (HAE : env_agree 32 (Ereg regs []) (Eimg (Ereg regs []))).
{ split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
sps_pc_to (BASE + AF_arg_s).
unfold cfg_at, w64 in K.
lazymatch goal with Hg : mem_grows (mrestrict _ mem) (mrestrict _ ?m1) |- _ => rename Hg into HGA end.
apply K.
- exact HJ.
- sps_keep_all.
- exact HGA.
- rewrite Q1. unfold SPS_RET_A2, AF_sup_policy_set. reflexivity.
- rewrite Q10. apply EEo. reflexivity.
- rewrite Q11. apply EEo. reflexivity.
- sps_kept HS HAE sps_kept_mid.
Qed.

(* --- arg_s's return to the call of rec_shape_of (0x8be44 .. 0x8be50): a0 := "policy_set", a1 := 10 --------- *)
Lemma sps_mid3 : forall (W : world SEGS) (regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall (regs1 : bvmap 5 word) mem1 md1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, rdW W mem1 a = rdW W mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
  getr regs1 1 = Z_to_bv 64 (BASE + SPS_RET_RSO) ->
  getr regs1 10 = w64 SPS_NAME -> getr regs1 11 = w64 (Z.of_nat (length sps_verb)) ->
  (forall r, In r sps_kept_mid -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_rec_shape_of) regs1 mem1 md1) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_RET_A2) regs mem md) Q.
Proof.
intros W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ K.
destruct (sps_seed0 W regs mem SPS_RET_A2) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EN : ew (Eimg (Ereg regs [])) (A_OBJ 71) = Z_to_bv 64 SPS_NAME).
{ rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite sps_name_val. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs []) (Eimg (Ereg regs []))).
{ split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
sps_pc_to (BASE + AF_rec_shape_of).
unfold cfg_at, w64 in K.
lazymatch goal with Hg : mem_grows (mrestrict _ mem) (mrestrict _ ?m1) |- _ => rename Hg into HGA end.
apply K.
- exact HJ.
- sps_keep_all.
- exact HGA.
- rewrite Q1. unfold SPS_RET_RSO, AF_sup_policy_set. reflexivity.
- rewrite Q10. first [exact EN | (change (A_OBJ 71) with 312%nat in EN; exact EN) | (rewrite <- EN; reflexivity)].
- rewrite Q11. reflexivity.
- sps_kept HS HAE sps_kept_mid.
Qed.

(* --- rec_shape_of's return, the epilogue and the tail jump into answer (0x8be54 .. 0x8be74) ------------------ *)
Lemma sps_epi : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
spZ regs = sp0 - SPS_FRAME -> 2 ^ 46 <= sp0 - SPS_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
sps_frame (rdW W mem) sp0 regs0 ->
(forall (regs1 : bvmap 5 word) mem1 md1,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, rdW W mem1 a = rdW W mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
  getr regs1 2 = w64 sp0 ->
  (forall r, In r sps_saved -> getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
  getr regs1 10 = getr regs 18 -> getr regs1 11 = getr regs 10 -> getr regs1 12 = w64 1 ->
  (forall r, In r sps_kept_epi -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_answer) regs1 mem1 md1) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_RET_RSO) regs mem md) Q.
Proof.
intros W regs regs0 mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ Hsp Hlo Hhi Hal HFR K.
destruct (sps_seedT W regs regs0 mem sp0 Hsp Hlo Hhi Hal HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (sps_extraT regs0)))) by apply Eimg_env.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (sps_extraT regs0))) m = getr regs rr)
  by (intros m rr Hm; apply ew_Eimg_Ereg_nat; exact Hm).
assert (EX : forall j, (j < 4)%nat -> ew (Eimg (Ereg regs (sps_extraT regs0))) (32 + j) = nth j (sps_extraT regs0) (Z_to_bv 64 0))
  by (intros j Hj; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (HAE : env_agree 32 (Ereg regs (sps_extraT regs0)) (Eimg (Ereg regs (sps_extraT regs0)))).
{ split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
remember (Eimg (Ereg regs (sps_extraT regs0))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - SPS_FRAME) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ sps_awr_lit. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (Z_to_bv 5 8) Q8. prreg HS (Z_to_bv 5 9) Q9.
prreg HS (Z_to_bv 5 18) Q18. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
sps_pc_to (BASE + AF_answer).
unfold cfg_at, w64 in K.
lazymatch goal with Hg : mem_grows (mrestrict _ mem) (mrestrict _ ?m1) |- _ => rename Hg into HGA end.
apply K.
- exact HJ.
- sps_keep_all.
- exact HGA.
- rewrite Q2, Usp; unfold w64, SPS_FRAME; f_equal; lia.
- intros r Hr. cbv [sps_saved In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]].
  + rewrite Q1. exact (EX 0%nat ltac:(lia)).
  + rewrite Q8. exact (EX 1%nat ltac:(lia)).
  + rewrite Q9. exact (EX 2%nat ltac:(lia)).
  + rewrite Q18. exact (EX 3%nat ltac:(lia)).
- rewrite Q10. apply EEo. reflexivity.
- rewrite Q11. apply EEo. reflexivity.
- rewrite Q12. reflexivity.
- sps_kept HS HAE sps_kept_epi.
Qed.

(* --- the call of rec_shape_of("policy_set", 10) at 0x8be50 ------------------------------------------------- *)
Variable MT : ameter_ops.
(* the statement's own Section hypothesis (sup_policy_set_c.v:73) *)
Hypothesis TREC_SHAPE_OF : trec_shape_of_spec B MT.
(* the per-binary record and the read-only premise the A walk takes under these names (A sup_policy_set.v:55-79) *)
Hypothesis HB : CmdBSyms B.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).

(* the verb literal as rec_shape_of's contract asks for it, through astr_argA's read-only arm (a Theorem Labs lane 917ca7ac6b1:
   cmd_addr_b / cmd_hull_b / the end in cmd_ro_ends, all by computation over the record's lists) *)
Lemma sps_verb_arg : forall ly S (rd : reader),
cmd_ro_ok rd -> Z.of_nat (length sps_verb) <= 16 ->
abytes_atR rd SPS_NAME sps_verb /\
(in_blockA (ablocks B ly S) SPS_NAME (Z.of_nat (length sps_verb)) \/
 astr_argA B ly S rd (in_roP SEGS CMD_RLO CMD_RHI) [] SPS_NAME (Some sps_verb)).
Proof.
intros ly S rd HROK _.
assert (HLIT : abytes_atR rd 0x21e80 RO_lit_21e80).
{ destruct HROK as [HBY _]. unfold cmd_ro_bytes in HBY. sps_proj HBY. }
assert (HLITro : forall i, 0 <= i < 11 -> in_roP SEGS CMD_RLO CMD_RHI (0x21e80 + i)).
{ pose proof CMD_RO_IN as HRI. unfold cmd_ro_in in HRI. sps_proj HRI. }
rewrite sps_verb_lit in HLIT. unfold SPS_NAME in *. split; [exact (sps_abytes_prefix _ _ _ _ HLIT)|].
right. cbn [astr_argA]. change (Z.of_nat (length sps_verb)) with 10. split; [lia|]. split.
{ split; [exact HLIT|]. intros Hz. cbn in Hz.
  repeat (destruct Hz as [Hz|Hz]; [apply (f_equal bv_unsigned) in Hz; vm_compute in Hz; discriminate Hz|]). exact Hz. }
split; [unfold LMAX; lia|]. right. split.
- intros i Hi. split; [apply HLITro; lia|]. rewrite (ts_owned B HB), (ts_errno B HB). split.
  + apply (sps_unowned_rng 0x21e80 11); [vm_compute; reflexivity | lia].
  + unfold TFIB_ERRNO. lia.
- split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  change (Z.of_nat (length sps_verb)) with 10. cbv [cmd_ro_ends]. repeat (first [left; reflexivity | right]).
Qed.

(* from arg_s's return (0x8be44) through the call of rec_shape_of to its return (0x8be54): the state after the call
   as the caller's walk continues from it *)
Lemma sps_rso : forall (W : world SEGS) (regs : bvmap 5 word) mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
spZ regs = sp0 - SPS_FRAME -> SPS_FRAME + REC_SHAPE_OF_STK <= STK ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
st_nev Sc + EV_REC_SHAPE_OF <= EV_MAX ->
(forall ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 memX mdX q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_REC_SHAPE_OF) ->
  ajournal SEGS B REC_SHAPE_OF_STK (sp0 - SPS_FRAME) [] lyc Sc W memX mdX [] ly2 S2 W2 mem2 md2 EV_REC_SHAPE_OF ->
  (forall a, rdW W memX a = rdW W mem a) ->
  (forall r, In r sps_kept_mid -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr regs2 10 = w64 q -> 0 <= q < 2 ^ 64 ->
  (forall O, astr_argA B ly2 S2 (rdW W2 mem2) (in_roP SEGS CMD_RLO CMD_RHI) O q (Some sps_shape)) ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> ly2 = lyc -> S2 = Sc ->
  SRr SEGS W2 (cfg_at SEGS (BASE + SPS_RET_RSO) regs2 mem2 md2) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + SPS_RET_A2) regs mem md) Q.
Proof.
intros W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ Hsp HSTK Hgp Htp HROD HROK HEV K.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
apply (sps_mid3 W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ).
intros regsX memX mdX HJX KX _ QX1 QX10 QX11 QXk.
assert (HRODX : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W memX)) by exact (sps_aro_kept _ _ _ B _ _ KX HROD).
assert (HROKX : cmd_ro_ok (rdW W memX)) by exact (sps_ro_ok_kept _ _ KX HROK).
assert (HBYTES := sps_verb_arg lyc Sc (rdW W memX) HROKX).
assert (QX2 : getr regsX 2 = getr regs 2).
{ pose proof (QXk 2 ltac:(cbv [sps_kept_mid]; repeat (first [left; reflexivity | right]))) as H.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (QX3 : getr regsX 3 = getr regs 3).
{ pose proof (QXk 3 ltac:(cbv [sps_kept_mid]; repeat (first [left; reflexivity | right]))) as H.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (QX4 : getr regsX 4 = getr regs 4).
{ pose proof (QXk 4 ltac:(cbv [sps_kept_mid]; repeat (first [left; reflexivity | right]))) as H.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (HspX : spZ regsX = sp0 + -32) by (unfold spZ; rewrite QX2; fold (spZ regs); unfold SPS_FRAME in Hsp; lia).
unfold cfg_at.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W regsX memX (w64 (BASE + AF_rec_shape_of)) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc mdX k REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr regsX 1) _ HJX HspX ltac:(reflexivity) ltac:(lia)
    ltac:(unfold REC_SHAPE_OF_STK, ESTACK; lia) ltac:(unfold SPS_FRAME in HSTK; lia)
    (eq_trans QX3 Hgp) (eq_trans QX4 Htp) eq_refl
    ltac:(rewrite QX1; apply ret_ok_codeptr_v; [unfold SPS_RET_RSO, AF_sup_policy_set; lia | reflexivity])
    ltac:(rewrite QX1; rewrite unsigned_lit_small by (unfold SPS_RET_RSO, AF_sup_policy_set; lia);
          unfold SPS_RET_RSO, AF_sup_policy_set; lia)).
  - intros HPREX.
    exact (TREC_SHAPE_OF lyc Sc W regsX memX mdX SPS_NAME sps_verb HPREX HRODX QX10 ltac:(unfold SPS_NAME; lia) QX11
      ltac:(vm_compute; reflexivity) HROKX VOBJS HBYTES HEV).
  - intros a (r & [] & _). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & HK4).
destruct HK4 as ((q & HQ10 & Hqb & Hq) & HPerm4 & Ely4 & ES4).
replace (mkCfg (mkst regs4 (getr regsX 1) mem4 (seg_rom SEGS)) md4) with (cfg_at SEGS (BASE + SPS_RET_RSO) regs4 mem4 md4)
  by (unfold cfg_at, w64; rewrite QX1; reflexivity).
replace (sp0 + -32) with (sp0 - SPS_FRAME) in HJc by (unfold SPS_FRAME; lia).
apply (K ly4 S4 W4 regs4 mem4 md4 memX mdX q HJ4 HJc KX).
- intros r Hr. rewrite (HP4 r (sps_kept_mid_saved r Hr)). exact (QXk r Hr).
- exact HQ10.
- exact Hqb.
- intros O. exact (Hq O).
- exact HPerm4.
- exact Ely4.
- exact ES4.
Qed.

End e.
End f.
End d.
