(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk kit of sup_pool_config on plugin-hostd/fuzz_command.asan (0x8bcfc, 97
   instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cgif_close's symbolic register files,
   regions, facts and seeds) and of lib/A/Prog/RecBTemplate.v (the recorder globals' zero-shadow
   ranges and the slot's shadow entry) over fuzz_command's listing. *)

(* The symbolic states of the walk. Atoms: 0..31 the registers, 32 the shadow base, 33 g_rec.ncalls at the entry,
   34 the slot c that the inlined record() picks (g_rec.calls[n] or record.spill), 35..41 the entry values of the
   seven registers the prologue saves (ra, s0..s5). Three seeds: the entry (0x8bcfc), the point where the two arms
   of record() meet (0x8bd78, s1 = c), and the call of xstrdup on the argument (0x8bdb4, after the default for a
   NULL name is chosen). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* program points, as listing offsets *)
Definition SPC_JOIN : Z := AF_sup_pool_config + 0x7c.   (* 0x8bd78: the two arms of record() meet *)
Definition SPC_DUP : Z := AF_sup_pool_config + 0xb8.    (* 0x8bdb4: mv a0,s2 before the call of xstrdup *)
Definition SPC_ARGI : Z := AF_sup_pool_config + 0x100.  (* 0x8bdfc: the return from arg_i *)
Definition SPC_RCF : Z := AF_sup_pool_config + 0x5c.    (* 0x8bd58: the return from rec_calls_free *)
(* the registers the prologue saves, from the top of the 64-byte frame: ra at sp+56 down to s5 at sp+8 *)
Definition spc_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
Definition spc_extra (regs : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) spc_saved.
Definition SPC_Bx : sv := SOff 32 0.
Definition SPC_SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition SPC_SH : list shent := [mkSHE 34 0 CALL_SIZE].
(* the shadow byte address of c + 4, in the form the token executor writes it *)
Definition spc_shx4 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 4) (SLit 3)) (SOff 32 0).

(* the entry state's regions: the frame, the GOT word of the shadow-base cell, the cell, g_rec.ncalls, the slot *)
Definition spc_frame0 : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [].
Definition spc_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition spc_slot_rg (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 34%nat) 0 CALL_SIZE 0 CALL_SIZE cs.
Definition spc_rs0 : smem := [spc_frame0; got_regionP; bcell_regionP 32; spc_ncalls; spc_slot_rg []].
Definition spc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 16 0);
         (34%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3); (A_OBJ 51, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].
Definition ss_spc0 : sstate := mkSS AF_sup_pool_config sr_atoms spc_rs0 None spc_facts0.

(* the mid-walk states: the frame (sp = entry sp - 64) holds the saved registers' entry values, read only *)
Definition spc_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
  (map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 7)).
Definition spc_factsM : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
         (34%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
Definition spc_regsJ : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 9 (SOff 34 0)) 20 (SOff 32 0).
Definition spc_regsD : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 9 (SOff 34 0)) 19 (SOff 34 4)) 20 (SOff 32 0)) 21 spc_shx4.
Definition spc_slot_fn0 : list YP09.chunk :=
[YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit REC_POOL_CONFIG))].
Definition ss_spcM (pc : Z) (sregs : list sv) (cs : list YP09.chunk) : sstate :=
mkSS pc sregs [spc_frame; spc_slot_rg cs] None spc_factsM.

(* the slot record() picks: an entry of g_rec's table or record.spill (RecBTemplate.v's rbt_slot_ok) *)
Definition spc_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_CALLS + CALL_SIZE * 16 /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma spc_slot_bounds : forall c, spc_slot_ok c -> A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *;
[split; [lia | exact H3] | split; [lia | reflexivity]].
Qed.

(* the two zero-shadow ranges of the record that hold the recorder's globals (AF0m.v Tfib_zero_shadow): g_rec's
   table ends the first, record.spill is the second *)
Definition SPC_ZSH_REC : Z * Z := (0xada00, 0x5e3b00 - 0xada00).
Definition SPC_ZSH_SPILL : Z * Z := (0x5e3be0, 0x5e3c18 - 0x5e3be0).
Lemma spc_zsh_rec_in : In SPC_ZSH_REC Tfib_zero_shadow.
Proof. unfold SPC_ZSH_REC, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.
Lemma spc_zsh_spill_in : In SPC_ZSH_SPILL Tfib_zero_shadow.
Proof. unfold SPC_ZSH_SPILL, Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.

Lemma spc_U_shx4 : forall E c, ew E 32 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 c -> 0 <= c -> c + 4 < 2 ^ 60 ->
U E spc_shx4 = SB + (c + 4) / 8.
Proof.
intros E c H32 H34 Hc0 Hc. unfold spc_shx4.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H32, H34.
rewrite !unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (c + 4) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (c + 4) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small (c + 4)) by lia. rewrite (YP0m.zcanon_small ((c + 4) / 8)) by lia.
rewrite (YP0m.zcanon_small SB) by (unfold SB; lia).
rewrite YP0m.zcanon_small by (unfold SB; lia). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma spc_E_saved : forall (regs regs1 : bvmap 5 word) n c j r, nth_error spc_saved j = Some r ->
ew (Eimg (Ereg regs1 (spc_extra regs n c))) (35 + j) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs1 n c j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some spc_saved j)); rewrite Hj; discriminate).
rewrite Eimg_low by (unfold A_TEXT; lia). replace (35 + j)%nat with (32 + S (S (S j)))%nat by lia. rewrite ew_Ereg_extra.
do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). lia.
Qed.

Lemma spc_E_lit : forall (regs regs1 : bvmap 5 word) n c,
ew (Eimg (Ereg regs1 (spc_extra regs n c))) 32 = Z_to_bv 64 SB /\
ew (Eimg (Ereg regs1 (spc_extra regs n c))) 33 = Z_to_bv 64 n /\
ew (Eimg (Ereg regs1 (spc_extra regs n c))) 34 = Z_to_bv 64 c.
Proof.
intros. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs1 _ 0) | split; [exact (ew_Ereg_extra regs1 _ 1) | exact (ew_Ereg_extra regs1 _ 2)]].
Qed.

Lemma spc_E_reg : forall (regs regs1 : bvmap 5 word) n c k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (Eimg (Ereg regs1 (spc_extra regs n c))) k = getr regs1 r.
Proof.
intros regs regs1 n c k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.


(* the saved registers' entry values in the frame: register spc_saved[j] at sp0 - 8 - 8 j *)
Definition spc_frame_at (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error spc_saved j = Some r -> val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

Lemma spc_frame_kept : forall H H' m m' sp0 regs,
spc_frame_at (mrestrict H m) sp0 regs -> (forall a, sp0 - 56 - 8 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
spc_frame_at (mrestrict H' m') sp0 regs.
Proof.
intros H H' m m' sp0 regs HF Hk j r Hj. pose proof (HF j r Hj) as V.
assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some spc_saved j)); rewrite Hj; discriminate).
intros kk Hkk. rewrite <- (V kk Hkk). apply (mbyte_of_aview SEGS). apply Hk. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.

Lemma spc_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma spc_spill_val : VAL (A_OBJ 51) = A_REC_SPILL.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma spc_verb_val : VAL (A_OBJ 68) = 0x21e80.
Proof. rewrite (VOBJS 68%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma spc_addressable_rec : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_G_REC <= a -> a + n <= A_G_REC + OFF_CALLS + CALL_SIZE * 16 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi. unfold A_G_REC, OFF_CALLS, CALL_SIZE in Hlo, Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md SPC_ZSH_REC a n HAR spc_zsh_rec_in
  ltac:(reflexivity) ltac:(reflexivity)
  ltac:(unfold SPC_ZSH_REC; cbn [fst snd]; lia) ltac:(unfold SPC_ZSH_REC; cbn [fst snd]; lia)).
Qed.

Lemma spc_addressable_spill : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_REC_SPILL <= a -> a + n <= A_REC_SPILL + SC_SIZE ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi. unfold A_REC_SPILL, SC_SIZE in Hlo, Hhi.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md SPC_ZSH_SPILL a n HAR spc_zsh_spill_in
  ltac:(reflexivity) ltac:(reflexivity)
  ltac:(unfold SPC_ZSH_SPILL; cbn [fst snd]; lia) ltac:(unfold SPC_ZSH_SPILL; cbn [fst snd]; lia)).
Qed.

Lemma spc_got_val : VAL (A_OBJ 0) = 0xa63f0.
Proof. rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma spc_cell_val : VAL (A_OBJ 12) = 0xb10b8.
Proof. rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma spc_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> spc_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(H1 & H2 & _) | ->].
- apply (spc_addressable_rec ly S W mem md); [exact HAR | unfold OFF_CALLS in H1; lia | exact H2].
- apply (spc_addressable_spill ly S W mem md); [exact HAR | lia | unfold SC_SIZE, CALL_SIZE; lia].
Qed.

Lemma spc_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma spc_sh_ok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> ew E 32 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 c -> spc_slot_ok c ->
sh_ok SEGS SPC_Bx SPC_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR E32 E34 Hc.
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
unfold sh_ok, SPC_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E SPC_Bx 34 c CALL_SIZE c 0 CALL_SIZE).
- exact (spc_slot_addressable ly S W mem md c HAR Hc).
- unfold SPC_Bx. rewrite (spc_U_atom E 32 SB E32) by (cbv [SB]; lia). reflexivity.
- apply spc_U_atom; [exact E34 | cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* the facts of the mid-walk states *)
Lemma spc_factsM_ok : forall E sp c,
ew E 2 = Z_to_bv 64 sp -> ew E 32 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 c ->
2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> spc_slot_ok c -> facts_ok E spc_factsM.
Proof.
intros E sp c E2 E32 E34 Hsp Hsp16 Hc.
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
unfold facts_ok, spc_factsM. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E32, E34.
rewrite !unsigned_lit_small by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat split; first [exact I | lia | exact Hsp16 | exact Hc8 | unfold SB; lia].
Qed.

(* the seed of a mid-walk segment at pc: sp is the entry sp0 - 64, the frame holds the saved registers, the slot
   c is writable and holds the chunks cs *)
Lemma spc_seed : forall pc sregs cs (W1 : world SEGS) (regs regs1 : bvmap 5 word) mem1 sp0 n c ly1 S1 md1,
AR SEGS B ly1 S1 W1 mem1 md1 ->
regions_wf [spc_frame; spc_slot_rg cs] = true ->
2 ^ 46 <= sp0 - 64 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> spc_slot_ok c ->
bv_unsigned (getr regs1 2) = sp0 - 64 ->
regs_ok (Eimg (Ereg regs1 (spc_extra regs n c))) sregs regs1 ->
spc_frame_at (mrestrict (w_H W1) mem1) sp0 regs ->
(forall a, c <= a < c + CALL_SIZE -> writable_at SEGS (mrestrict (w_H W1) mem1) a) ->
Forall (YP09.chunk_ok SEGS (Eimg (Ereg regs1 (spc_extra regs n c))) (mrestrict (w_H W1) mem1) c) cs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (spc_extra regs n c))) (ss_spcM pc sregs cs)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS SPC_Bx SPC_SH (Eimg (Ereg regs1 (spc_extra regs n c))) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs cs W1 regs regs1 mem1 sp0 n c ly1 S1 md1 HAR Hwf Hsp46 Hsp47 Hal Hc Hsp HREG HFR HWC HCS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
set (E := Eimg (Ereg regs1 (spc_extra regs n c))).
destruct (spc_E_lit regs regs1 n c) as (E32 & _ & E34). fold E in E32, E34.
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 64)).
{ subst E. rewrite (spc_E_reg regs regs1 n c 2 2%bv eq_refl). apply bv_eq. rewrite Hsp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (B2 : base_val E (Some 2%nat) = sp0 - 64) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (B34 : base_val E (Some 34%nat) = c) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
rewrite restrict_mkst_fx.
split; [| exact (spc_sh_ok ly1 S1 W1 mem1 md1 E c HAR E32 E34 Hc)].
unfold ss_spcM. apply pa_entry_st_ok_full.
- exact HREG.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold YP09.region_ok.
  + unfold spc_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
    let j := eval compute in (k - 35)%nat in let r := eval compute in (nth j spc_saved 0) in
    apply (chunk_ok_val SEGS E _ (sp0 - 64) off 8 (SOff k 0) (bv_unsigned (ew E k)));
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E k)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
    | cbn; lia
    | replace (sp0 - 64 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
      let Ej := fresh "Ej" in pose proof (spc_E_saved regs regs1 n c j r eq_refl) as Ej; change (35 + j)%nat with k in Ej;
      fold E in Ej; rewrite Ej; exact (HFR j r eq_refl) ] end.
  + unfold spc_slot_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B34. split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold CALL_SIZE, A_REC_SPILL in *; lia|]. split.
    { intros o Ho. apply HWC. unfold CALL_SIZE in *. lia. }
    exact HCS.
- apply pairwise_disjoint_of_extents. unfold spc_frame, spc_slot_rg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- exact (spc_factsM_ok E (sp0 - 64) c E2 E32 E34 ltac:(lia) ltac:(rewrite Zminus_mod, Hal; reflexivity) Hc).
Qed.

(* the seed of the last segment (from the return of arg_i): the frame only, the slot written no more *)
Definition ss_spcF (pc : Z) (sregs : list sv) : sstate := mkSS pc sregs [spc_frame] None spc_factsM.
Lemma spc_seed_fr : forall pc sregs (W1 : world SEGS) (regs regs1 : bvmap 5 word) mem1 sp0 n c ly1 S1 md1,
AR SEGS B ly1 S1 W1 mem1 md1 ->
2 ^ 46 <= sp0 - 64 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> spc_slot_ok c ->
bv_unsigned (getr regs1 2) = sp0 - 64 ->
regs_ok (Eimg (Ereg regs1 (spc_extra regs n c))) sregs regs1 ->
spc_frame_at (mrestrict (w_H W1) mem1) sp0 regs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (spc_extra regs n c))) (ss_spcF pc sregs)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS SPC_Bx SPC_SH (Eimg (Ereg regs1 (spc_extra regs n c))) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs W1 regs regs1 mem1 sp0 n c ly1 S1 md1 HAR Hsp46 Hsp47 Hal Hc Hsp HREG HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
set (E := Eimg (Ereg regs1 (spc_extra regs n c))).
destruct (spc_E_lit regs regs1 n c) as (E32 & _ & E34). fold E in E32, E34.
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 64)).
{ subst E. rewrite (spc_E_reg regs regs1 n c 2 2%bv eq_refl). apply bv_eq. rewrite Hsp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (B2 : base_val E (Some 2%nat) = sp0 - 64) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
split; [| exact (spc_sh_ok ly1 S1 W1 mem1 md1 E c HAR E32 E34 Hc)].
unfold ss_spcF. apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]; unfold YP09.region_ok.
  unfold spc_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
  let j := eval compute in (k - 35)%nat in let r := eval compute in (nth j spc_saved 0) in
  apply (chunk_ok_val SEGS E _ (sp0 - 64) off 8 (SOff k 0) (bv_unsigned (ew E k)));
  [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E k)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
  | cbn; lia
  | replace (sp0 - 64 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
    let Ej := fresh "Ej" in pose proof (spc_E_saved regs regs1 n c j r eq_refl) as Ej; change (35 + j)%nat with k in Ej;
    fold E in Ej; rewrite Ej; exact (HFR j r eq_refl) ] end.
- apply pairwise_disjoint_of_extents. unfold spc_frame, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2.
  cbn [zpairwise_disjoint zall_disjoint]. exact (conj I I).
- exact (spc_factsM_ok E (sp0 - 64) c E2 E32 E34 ltac:(lia) ltac:(rewrite Zminus_mod, Hal; reflexivity) Hc).
Qed.

(* the seed of the entry segment: every register its own atom; the frame below sp, the shadow base's GOT word and
   cell, g_rec.ncalls holding n, and the slot c writable *)
Lemma spc_entry_seed : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) n c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs - 64 -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 -> spc_slot_ok c ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
(forall a, A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4 -> writable_at SEGS (mrestrict (w_H W) mem) a) ->
(forall a, c <= a < c + CALL_SIZE -> writable_at SEGS (mrestrict (w_H W) mem) a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (spc_extra regs n c))) ss_spc0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_pool_config)) mem (seg_rom SEGS)))
/\ sh_ok SEGS SPC_Bx SPC_SH (Eimg (Ereg regs (spc_extra regs n c))) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs n c HAR Hsp46 Hsp47 Hal Hpres Hn Hc HNC HWN HWC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := Eimg (Ereg regs (spc_extra regs n c))).
destruct (spc_E_lit regs regs n c) as (E32 & E33 & E34). fold E in E32, E33, E34.
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (spc_E_reg regs regs n c 2 2%bv eq_refl)).
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite spc_grec_val; reflexivity).
assert (ES : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL)
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite spc_spill_val; reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite E2; reflexivity).
split; [| exact (spc_sh_ok ly S W mem md E c HAR E32 E34 Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold spc_rs0, spc_frame0, got_regionP, bcell_regionP, spc_ncalls, spc_slot_rg.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite B2. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)) as HV; change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split; [intros o Ho; apply HWN; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
  + rewrite (VB 34%nat c E34) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    split; [unfold A_G_REC, OFF_CALLS in *; lia|]. split; [unfold CALL_SIZE, A_REC_SPILL in *; lia|].
    split; [intros o Ho; apply HWC; unfold CALL_SIZE in *; lia | constructor].
- apply pairwise_disjoint_of_extents.
  unfold spc_rs0, spc_frame0, got_regionP, bcell_regionP, spc_ncalls, spc_slot_rg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite spc_got_val, spc_cell_val.
  rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 34%nat c E34) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  rewrite B2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS, CALL_SIZE, A_REC_SPILL, OFF_CALLS in *.
  repeat split; lia.
- unfold facts_ok, spc_facts0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E32, E33, E34, EG, ES.
  change (bv_unsigned (getr regs 2)) with (spZ regs).
  rewrite !unsigned_lit_small by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat split; first [exact I | lia | exact Hal | exact Hc8 | unfold SB; lia | reflexivity].
Qed.

End e.
End f.
End d.
