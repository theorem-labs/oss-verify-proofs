(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_refusal's ASan walk (plugin-hostd/fuzz_command, 0x87f08), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry) and A/AChc.v: the symbolic entry state with the GOT words of g_rec and g_quitting, the two read fields of g_rec and the word g_quitting, the shadow entries that make the three inline checks vanish, and the seed lemma; plus the transport of the read-only facts across the function's own frame writes. *)
(* Modified by Theorem Labs, 2026-10: ported from lib/A/Prog/check_refusal_s1.v (the A walk's kit) to fuzz_command.asan-ubsan (image B, check_refusal at 0x88204): module paths, and the B image's addresses of g_rec (0x5e32c0), g_quitting (0x5e37e0), their GOT words (0xa6bc8, 0xa6be0), the shadow base's GOT word (0xa5f50) and the shadow-base cell (0xb0c38). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* reads that are the same outside a window [lo, hi) *)
Definition cr_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma cr_abytes_kept : forall rd rd' lo hi p l, cr_kept rd rd' lo hi -> abytes_atR rd p l ->
0 <= p -> p + Z.of_nat (length l) <= lo -> lo < 2 ^ 64 -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hlo i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma cr_astr_kept : forall rd rd' lo hi p s, cr_kept rd rd' lo hi -> astr_atR rd p s ->
0 <= p -> p + Z.of_nat (length s) + 1 <= lo -> lo < 2 ^ 64 -> astr_atR rd' p s.
Proof.
intros rd rd' lo hi p s HK [H1 H2] Hp Hl Hlo. split; [|exact H2].
apply (cr_abytes_kept rd rd' lo hi p _ HK H1 Hp); [rewrite length_app; cbn [length]; lia | exact Hlo].
Qed.
Lemma cr_aval_kept : forall rd rd' lo hi a n v, cr_kept rd rd' lo hi -> aval_mem rd a n v ->
0 <= a -> a + Z.of_nat n <= lo -> lo < 2 ^ 64 -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v HK H Ha Hl Hlo k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma cr_rd32_kept : forall rd rd' lo hi a v, cr_kept rd rd' lo hi -> rd32 rd a v ->
0 <= a -> a + 4 <= lo -> lo < 2 ^ 64 -> rd32 rd' a v.
Proof. intros rd rd' lo hi a v HK H Ha Hl Hlo k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma cr_rdword_kept : forall rd rd' lo hi a v, cr_kept rd rd' lo hi -> rdword rd a = Some v ->
0 <= a -> a + 8 <= lo -> lo < 2 ^ 64 -> rdword rd' a = Some v.
Proof. intros rd rd' lo hi a v HK H Ha Hl Hlo. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK; lia. Qed.
(* every byte cmd_ro_ok names lies below the image's end *)
Lemma cr_ro_ok_kept : forall rd rd' lo hi, cr_kept rd rd' lo hi -> 0x606000 <= lo -> lo < 2 ^ 64 ->
cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' lo hi HK Hlo Hlo2 [HB HT]. split.
- unfold cmd_ro_bytes in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply (cr_abytes_kept rd rd' lo hi); [exact HK | eassumption | lia | cbn; lia | exact Hlo2]).
- intros e He a Ha. rewrite (HK a); [exact (HT e He a Ha) | |].
  + pose proof (proj1 (forallb_forall (fun x => (0x10000 <=? x) && (x <? 0x605ff0)) cmd_ro_ends)
      ltac:(vm_compute; reflexivity) e He) as Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia.
  + pose proof (proj1 (forallb_forall (fun x => (0x10000 <=? x) && (x <? 0x605ff0)) cmd_ro_ends)
      ltac:(vm_compute; reflexivity) e He) as Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H2.
    pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia.
Qed.
(* an n-wide field read through the world's view is the same field of the restricted memory *)
Lemma cr_val_of_aval : forall segs H (mem : word -> option byte) a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

Definition CR_SB : Z := 0x7fff8000.
Definition CRx : sv := SOff 32 0.
Definition CRspan : Z * Z := (CR_SB, CR_SB + 2 ^ 44 - 1).
(* atoms: 32 the shadow base, 33 g_quitting's address, 34 g_rec.reply, 35 g_rec.state, 36 g_quitting's word;
   g_rec itself is the listing's object A_OBJ 44 (0x5e32c0), its GOT word A_OBJ 2 (0xa6bc8), g_quitting's GOT word
   A_OBJ 6 (0xa6be0) *)
Definition cr_regions : smem :=
[ stack_region 32;
  YP09.mkRegion (Some (A_OBJ 44)) 928 952 0 0 [YP09.mkChunk 928 (CVal 8 (SOff 34 0)); YP09.mkChunk 944 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some (A_OBJ 6)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))];
  got_regionP; bcell_regionP 32;
  YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 44) 0))] ].
Definition cr_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF CR_SB CR_SB 0); (33%nat, mkAF A_G_QUITTING A_G_QUITTING 5);
  (34%nat, mkAF 0 (2^64-1) 0); (35%nat, mkAF 0 (2^64-1) 0); (36%nat, mkAF 0 (2^32-1) 0);
  (A_OBJ 44, mkAF A_G_REC A_G_REC 6) ] [] [].
Definition ss_cr : sstate := mkSS AF_check_refusal sr_atoms cr_regions None cr_facts.
Definition cr_SH : list shent := [mkSHE (A_OBJ 44) 0 960; mkSHE 33 0 4].
Definition cr_extra (reply state quit : Z) : list word := map (Z_to_bv 64) [CR_SB; A_G_QUITTING; reply; state; quit].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition cr_E (regs : bvmap 5 word) (reply state quit : Z) : env := Eimg (Ereg regs (cr_extra reply state quit)).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
Lemma cr_val_obj : forall i v, (i < length cmd_objs)%nat -> nth i cmd_objs 0 = v -> VAL (A_OBJ i) = v.
Proof. intros i v Hi Hv. rewrite (VOBJS i Hi). exact Hv. Qed.
Lemma cr_ew_obj : forall E i v, img_env VAL A_LIM E -> (i < length cmd_objs)%nat -> nth i cmd_objs 0 = v ->
  (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros E i v HE Hi Hv Hl. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)) as H.
rewrite (cr_val_obj i v Hi Hv) in H. pose proof (pa_val_range (A_OBJ i)) as R. rewrite (cr_val_obj i v Hi Hv) in R.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* the GOT words of g_rec and g_quitting, read from cmd_ro_ok's bytes (CmdRo.v RO_ptr_a6bc8, RO_ptr_a6be0) *)
Lemma cr_aval8_of_bytes : forall rd a l v, abytes_atR rd a l -> length l = 8%nat ->
  (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hk8. rewrite (H k) by (rewrite Hl; exact Hk8). f_equal. exact (Hk k Hk8). Qed.
Lemma cr_got_of_ro : forall rd, cmd_ro_ok rd -> aval_mem rd 0xa6bc8 8 A_G_REC /\ aval_mem rd 0xa6be0 8 A_G_QUITTING.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
assert (H1 : abytes_atR rd 0xa6bc8 RO_ptr_a6bc8).
{ clear - HRO. repeat match type of HRO with
  | abytes_atR _ 0xa6bc8 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO end. }
assert (H2 : abytes_atR rd 0xa6be0 RO_ptr_a6be0).
{ clear - HRO. repeat match type of HRO with
  | abytes_atR _ 0xa6be0 _ /\ _ => exact (proj1 HRO)
  | abytes_atR _ 0xa6be0 _ => exact HRO
  | _ /\ _ => apply proj2 in HRO end. }
split; (eapply cr_aval8_of_bytes; [eassumption | reflexivity |]);
  intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
Lemma cr_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md reply state quit,
AR SEGS B ly S W mem md ->
astk_ok (32 + 12288) ly (spZ regs) ->
(forall a, spZ regs - (32 + 12288) <= a < spZ regs -> apresent (w_H W) mem a) ->
aval_mem (rdW W mem) 0xa6bc8 8 A_G_REC -> aval_mem (rdW W mem) 0xa6be0 8 A_G_QUITTING ->
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 reply -> 0 <= reply < 2 ^ 64 ->
aval_mem (rdW W mem) (A_G_REC + OFF_STATE) 8 state -> 0 <= state < 2 ^ 64 ->
aval_mem (rdW W mem) A_G_QUITTING 4 quit -> 0 <= quit < 2 ^ 32 ->
range_addressable (rdW W mem) SHADOW_OFF A_G_REC 960 ->
range_addressable (rdW W mem) SHADOW_OFF A_G_QUITTING 4 ->
st_ok_pi SEGS VAL (cr_E regs reply state quit) ss_cr
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_refusal)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CRx cr_SH (cr_E regs reply state quit) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md reply state quit HAR Hstk Hpres G2 G6 Hrep Rrep Hst Rst Hq Rq ZREC ZQ.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := cr_E regs reply state quit).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cr_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cr_extra reply state quit)) n)
  by (intros n Hn; subst E; unfold cr_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 CR_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 A_G_QUITTING) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 reply) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 state) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 quit) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 0xa5f50) by (apply cr_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO2 : ew E (A_OBJ 2) = Z_to_bv 64 0xa6bc8) by (apply cr_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO6 : ew E (A_OBJ 6) = Z_to_bv 64 0xa6be0) by (apply cr_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 0xb0c38) by (apply cr_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO44 : ew E (A_OBJ 44) = Z_to_bv 64 0x5e32c0) by (apply cr_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (apply cr_val_obj; [vm_compute; lia | reflexivity]).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (apply cr_val_obj; [vm_compute; lia | reflexivity]).
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cr. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold cr_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cr_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 44) 0x5e32c0 EO44) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ 0x5e32c0 928 8 _ reply); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cr_val_of_aval SEGS _ mem _ 8 reply Hrep).
      -- apply (chunk_ok_val SEGS E _ 0x5e32c0 944 8 _ state); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cr_val_of_aval SEGS _ mem _ 8 state Hst).
    * rewrite (VB (A_OBJ 6) 0xa6be0 EO6) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa6be0 0 8 _ A_G_QUITTING); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_QUITTING; zside | zside |].
      rewrite Z.add_0_r. exact (cr_val_of_aval SEGS _ mem _ 8 _ G6).
    * rewrite (VB 33%nat A_G_QUITTING E33) by (unfold A_G_QUITTING; lia). unfold A_G_QUITTING. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0x5e37e0 0 4 _ quit); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (cr_val_of_aval SEGS _ mem _ 4 quit Hq).
    * rewrite (VB (A_OBJ 0) 0xa5f50 EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa5f50 0 8 (SOff (A_OBJ 12) 0) 0xb0c38);
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 12) 0xb0c38 EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xb0c38 0 8 (SOff 32 0) CR_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold CR_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite (VB (A_OBJ 2) 0xa6bc8 EO2) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa6bc8 0 8 (SOff (A_OBJ 44) 0) A_G_REC);
        [cbn [sv_denot]; rewrite EO44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_REC; zside | zside |].
      rewrite Z.add_0_r. exact (cr_val_of_aval SEGS _ mem _ 8 _ G2).
  + apply pairwise_disjoint_of_extents. unfold cr_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 44) 0x5e32c0 EO44), (VB (A_OBJ 6) 0xa6be0 EO6), (VB 33%nat A_G_QUITTING E33),
      (VB (A_OBJ 0) 0xa5f50 EO0), (VB (A_OBJ 12) 0xb0c38 EO12), (VB (A_OBJ 2) 0xa6bc8 EO2) by (unfold A_G_QUITTING; lia).
    cbn [base_val]. rewrite Usp. unfold A_G_QUITTING.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 Hstk0. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, E34, E35, E36, EO44, !unsigned_lit_small by (unfold CR_SB, A_G_QUITTING, A_G_REC; lia).
    unfold CR_SB, A_G_QUITTING, A_G_REC. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 Rrep Rst Rq. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, cr_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E CRx (A_OBJ 44) A_G_REC 960 A_G_REC 0 960 ZREC).
    * unfold U, CRx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite EO44, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold A_G_REC, SHADOW_OFF in *. cbn in Hx. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E CRx 33 A_G_QUITTING 4 A_G_QUITTING 0 4 ZQ).
    * unfold U, CRx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold A_G_QUITTING; lia). reflexivity.
    * lia. * lia.
    * intros x Hx. unfold A_G_QUITTING, SHADOW_OFF in *. cbn in Hx. lia.
Qed.
End e.
End f.
End d.
