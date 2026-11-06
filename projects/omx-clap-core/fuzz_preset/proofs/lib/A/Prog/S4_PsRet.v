(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string, image A): the two TAIL stretches of the walk, proved against the
   contract S4_PsBase.v (this row's; at walk-S4-gp blob a59ce5bfcbe3), in the GENERIC-P form (a Theorem Labs lane
   12:18Z): ps_ret0_walkP : ps_seg_ret0P P (from PS_RET0) and ps_retok_walkP : ps_seg_retokP P (from PS_RETOK), each
   ending in ps_postP P D, for every P with srr_inv_laws segs P (call-free: no srr_inv_call). Each stretch's one engine
   run goes through its YSRrMemnorm twin (paj_run_x_inv / paj_run_tok_x_inv, now YC1fPx.v 7814b594066f) at P, laws
   PLAW, premise the carry's P mem; the return leaves ms_mem as it is, so the post's P mem' is the run's HPM. The
   stable ps_ret0_walk / ps_retok_walk are the P := (fun _ => True) corollaries, statements byte-identical.
   FILE SET: as the kit's cut 7cdbb61b5fa0 carries it (PRH_Base blob ef7c8ca98529, PRH_FnReader blob f1ae32e3b2cd); the
   unit's set of record was, as S4_PsBase.v at 1503ed77ab4: the kit walkkit 9d109484e53, engine files and YCbqG.v by path
   from a working branch 63997a07aa6, PRW_StepKit / PRW_HShadow by path from walk-S7B b77dc99e0b5, PRW_CallerJ of walk-S4.
   THE CODE (the neutral listing of the image of record, the internal file parse_string.fuzz_preset.asan.s, byte-identical to
   the internal file neutral_dis.py on omx-clap-core-preset-ranout/asan; every offset is a DERIVED byte offset from parse_string's
   entry, the listing's A_prog_slot AS_parse_string):
     1284  li s2, 0                          PS_RET0: the join of every refusing path
     1288  mv a0, s2                         the epilogue, run by both stretches
     1292..1340  the 13 reloads: ra 136, s0 128, s1 120, s2 112, s3 104, s4 96, s5 88, s6 80, s7 72, s8 64, s9 56,
           s10 48, s11 40 off the body sp (DERIVED frame offsets; ps_saved)
     1344  addi sp, sp, 144                  (LENGTH: PS_FRAME)
     1348  ret
     1352  srli a0, s3, 3; add a0, a0, s8; lb a0, 0(a0); bnez a0 -> 1392 (the partial granule path, back to 1368)
     1368  sb zero, 0(s3)                    the NUL store at w, inside the new block
     1372  lbu a0, 0(s7); bnez a0 -> 1548    the shadow byte of q (errpath_store8)
     1380  addi s4, s4, 1
     1384  sd s4, 0(s0)                      the caller's cursor word, the one cell of FP = [(q, q + 8)]
     1388  j 1288
   Each stretch is ONE symbolic run to the `ret`, the frame region (the 13 saved registers as the entry's atoms)
   carried in its state, so the epilogue is checked by the engine on both paths and closed by the same argument
   (YCbqGwild.fpostW_xb_of_kept at the text's budget wbudget CW 0, the journal, cj_kept, aregs_preserved_of_st_ok;
   ret0's cut carries a BUDGETED journal - the bad escape's fuzz_free - which the run takes rebased,
   YCbqGwild.ajournal_xw_rebase, and the post unbases, ajournal_xw_unbase0). ret0 writes nothing; retok's two stores
   are read off the final symbolic state and the rest of memory is the pre-run one (the run's frame_of).
   Numerals: 144 (LENGTH: PS_FRAME, checked by vm_compute), the frame offsets -8 .. -104 off the entry sp (DERIVED:
   PS_FRAME - 136 .. PS_FRAME - 40), 1284 / 1288 / 1352 (DERIVED offsets), atom indices 0..64, 512 / 513 (DERIVED: the
   symbolic engine's numbering: 0..31 the entry registers, 32..63 the current registers, 64 the epilogue's shadow base
   atom, 512 / 513 the run's fresh token atoms), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (DERIVED: shadow and stack bounds), 4096
   (LENGTH: a page), 8 (LENGTH: a word). No ADDRESS literal.
   SECTION HYPOTHESES beyond the base's (both owned and discharged where the base's are, S4_PsTop): PST_ok (the base's
   own hypothesis, same text: the ledger's statics are image bytes) and HW : prh_head_wide (the kit's, discharged at the
   preset instance by a Theorem Labs lane's preset_head_wide); retok uses both, ret0 neither. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
(* the budgeted post of the batch text (fpostW_xb_of_kept) and the budget adapters (rebase / unbase0), qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the memnorm keep's runner side (the cut's YSRrMemnorm.v 5ffa8525936b Requires YAkMemnorm 96c72061b4d4 only, so no
   LiaTwx2 `lia ::=` reaches this file) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ S4_PsBase.
(* the re-hiding move: SRrG / SRr_SRrG / wle' (YA0nH), and the kept relation over a world relation R
   (YCbqGcallW.cj_keptR, qualified: KEPT below is PRW_CallerJ's cj_kept, the same body) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state shapes (no image value: atoms only) ---- *)
(* (the epilogue starts at 1288, DERIVED, inside both runs) *)
(* the current registers as the environment's atoms 32..63 *)
Definition ps_cur (regs : bvmap 5 word) : list word := map (getr regs) all_regs.
(* the register file at 1284 / 1288: every register is its current atom, but sp (the entry sp atom 2 minus the frame)
   and gp / tp (the entry's atoms: ps_gptp) *)
Definition ps_sr_epi : list sv :=
  SLit 0 :: SOff 33 0 :: SOff 2 (-144) :: SOff 3 0 :: SOff 4 0 :: map (fun i => SOff (32 + i) 0) (seq 5 27).
(* parse_string's frame below the entry sp (atom 2), read-only here: the 13 saved registers as the entry's atoms *)
Definition ps_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 0 0
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27 0)) ].
Definition ps_facts_epi : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition PS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PS_Bx_epi : sv := SOff 64 0.
(* ---- the state at PS_RETOK: the same register atoms, but s7 (x23) in the SHAPE the ASan token engine matches
   (the shadow cell of s0 = q: (q >> 3) + s8), the one written byte at w = s3 (atom 51) and the caller's cursor
   word at q = s0 (atom 40). DERIVED atom indices: 32 + the register number. ---- *)
Definition ps_sr_retok : list sv :=
  [SLit 0; SOff 33 0; SOff 2 (-144); SOff 3 0; SOff 4 0;
   SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0;
   SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 53 0; SOff 54 0;
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SOff 56 0);
   SOff 56 0; SOff 57 0; SOff 58 0; SOff 59 0; SOff 60 0; SOff 61 0; SOff 62 0; SOff 63 0].
Definition ps_w_region : YP09.region := YP09.mkRegion (Some 51%nat) 0 1 0 1 [].
Definition ps_q_region : YP09.region := YP09.mkRegion (Some 40%nat) 0 8 0 8 [].
Definition ps_facts_retok : facts :=
  mkFacts [(51%nat, mkAF 4096 (2 ^ 47 - 8) 0); (40%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
           (56%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ps_SH_retok : list shent := [mkSHE 51 0 1; mkSHE 40 0 8].
Definition PS_Bx_retok : sv := SOff 56 0.

Section pr. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
#[local] Notation PST := (prh_pst ).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept SK segs B PST).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the generic invariant (a Theorem Labs lane 12:18Z): call-free stretches take srr_inv_laws only *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.

(* ---- the environment: atoms 0..31 the entry registers, 32..63 the current ones ---- *)
Lemma ps_ew_hi : forall R X n, (32 <= n < A_TEXT)%nat -> ew (Eimg (Ereg R X)) n = nth (n - 32) X (Z_to_bv 64 0).
Proof.
intros R X n Hn. rewrite Eimg_low by lia. unfold Ereg. cbn [ew].
replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
Lemma ps_ew_lo : forall R X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg R X)) n = getr R r.
Proof.
intros R X n r H. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat R X n r H).
Qed.
Ltac ps_reg_tac Hsp Hgp Htp HFR :=
  match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | rewrite (ps_ew_lo _ _ 2 2 eq_refl), Hsp; unfold w64, PS_SP, spZ; rewrite HFR; f_equal; lia
  | rewrite (ps_ew_lo _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
  | rewrite (ps_ew_lo _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp ].


Lemma ps_regs_ok_epi : forall D regs, getr regs 2 = w64 (PS_SP D) -> ps_gptp D regs ->
  regs_ok (Eimg (Ereg (pi_regs D) (ps_cur regs))) ps_sr_epi regs.
Proof.
intros D regs Hsp [Hgp Htp]. assert (HFR : PS_FRAME = 144) by (vm_compute; reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ps_reg_tac Hsp Hgp Htp HFR|]). destruct Hr.
Qed.

(* s7's SHAPE at PS_RETOK: the shadow cell of q, as the ASan token engine writes it *)
Lemma ps_s7_denot : forall E q, bv_unsigned (ew E 40) = q -> bv_unsigned (ew E 56) = SHADOW_OFF ->
  0 <= q < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SOff 56 0)) = w64 (SHADOW_OFF + q / 8).
Proof.
intros E q H40 H56 Hq. cbn [sv_denot]. rewrite H40, H56, !Z.add_0_r.
assert (Hd : 0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite !(Z.mod_small (q / 8)) by lia. rewrite (Z.mod_small (q / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
lia.
Qed.

Ltac ps_reg2 Hsp Hgp Htp HFR Hs7e :=
  match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  first
  [ rewrite Hs7e; assumption
  | cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (ps_ew_lo _ _ 2 2 eq_refl), Hsp; unfold w64, PS_SP, spZ; rewrite HFR; f_equal; lia
    | rewrite (ps_ew_lo _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
    | rewrite (ps_ew_lo _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp ] ].

Lemma ps_regs_ok_retok : forall D regs, getr regs 2 = w64 (PS_SP D) -> ps_gptp D regs -> ps_sh_regs D regs ->
  getr regs 8 = w64 (pi_q D) -> 0 <= pi_q D < 2 ^ 47 ->
  regs_ok (Eimg (Ereg (pi_regs D) (ps_cur regs))) ps_sr_retok regs.
Proof.
intros D regs Hsp [Hgp Htp] (Hs8 & Hs7 & _) Hq8 Hqr.
assert (HFR : PS_FRAME = 144) by (vm_compute; reflexivity).
assert (E40 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 40) = pi_q D)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite Hq8; unfold w64; apply unsigned_lit_small; lia).
assert (E56 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 56) = SHADOW_OFF)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite Hs8; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (ps_s7_denot _ _ E40 E56 Hqr) as Hs7e.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ps_reg2 Hsp Hgp Htp HFR Hs7e|]). destruct Hr.
Qed.

(* the block the one fuzz_malloc made is NOT a block of the entry state *)
Lemma ps_newblk : forall D ly S Hp W mem md out Q,
  ps_alloc B D ly S Hp W mem out Q -> ARx ly S Hp W mem md ->
  ~ In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B (pi_ly D) (pi_S D)).
Proof.
intros D ly S Hp W mem md out Q HAL HAR Hin.
pose proof cf_head_nonneg as CH0.
pose proof HAL as (_ & _ & _ & _ & Hab & _).
assert (Hin' : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
assert (Hrq : 0 < req_size (Z.of_nat Q + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
rewrite Hab in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (out - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
  (out - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the kept relation does not look at the model's materialised pages *)
Lemma ps_kept_md : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3,
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.

Ltac ps_chunk Ei Hs HFR :=
  lazymatch goal with |- YP09.chunk_ok _ ?E0 ?m ?b {| c_off := ?o; YP09.c_val := CVal 8 ?e |} =>
  lazymatch type of Hs with val_mem _ _ _ _ ?v =>
    apply (chunk_ok_val _ E0 m b o 8 e v);
    [ cbn [sv_denot]; rewrite Ei, Z.add_0_r; reflexivity
    | lazymatch goal with |- 0 <= ?vv < _ => replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity;
        try unfold raZ; apply u64_range end
    | cbn; lia
    | lazymatch type of Hs with val_mem _ _ ?a _ _ => replace (b + o) with a by (unfold PS_SP; rewrite HFR; lia) end;
      exact Hs ]
  end end.

(* the kept relation over R does not look at the model's materialised pages either *)
Lemma ps_kept_mdR : forall (R : world segs -> world segs -> Prop) STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3,
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  same_but_materialized md2 md3 ->
  YCbqGcallW.cj_keptR (SK := SK) segs B PST R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.

(* ---- STRETCH 1: the NULL return, from PS_RET0: li s2, 0; the epilogue at 1288; ret. No store: the memory after the
   run is the memory before it. Over a world relation R (reflexive, transitive, containing wle): the NULL return is
   reached on both sides of the bad escape's fuzz_free, before it at wle (ps_ret0_walkP below, its instance), after it
   with the cut at wle' segs RZ_cf (S4_PsTop instantiates R there). The cut's journal is at a BUDGET WS (the bad
   escape's fuzz_free may store a cursor trace); the run takes it at the rebased entry state
   (YCbqGwild.ajournal_xw_rebaseR: budget [] from the entry with the cut's depot) with the runner over R
   (YC1fPx.paj_run_x_invR), and the post puts the budget back (ajournal_xw_unbase0R at the cut's wild-part inclusion)
   in the close over R (YCbqGwild.fpostW_xb_of_keptR); the return step is the plain one (paj_ret_at), lifted by
   YA0nH.SRr_SRrG. ---- *)
Theorem ps_ret0_walkPR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle segs W W' -> R W W') ->
  ps_seg_ret0PR B ARx SK P R CTX CW.
Proof.
intros R Rr Rt Rsub D ly S Hp W regs mem md HPRE ((k & WS & HBW & HJw & HK & HSV & _ & _ & HMN) & HGT & Hsp & HRL & HBB & HQ).
pose proof (ajxR_wild HJw) as HWI.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
clear HJw.
pose proof HPRE as ((HPX & _) & _).
pose proof HPX as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HFR : PS_FRAME = 144) by (vm_compute; reflexivity).
assert (Rsp : 2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47) by lia.
pose proof (ps_regs_ok_epi D regs Hsp HGT) as HRO.
assert (E1 : ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 1 = getr (pi_regs D) 1) by exact (ps_ew_lo _ _ 1 1 eq_refl).
assert (HAE : env_agree 32 (Ereg (pi_regs D) (ps_cur regs)) (Eimg (Ereg (pi_regs D) (ps_cur regs))))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg (pi_regs D) (ps_cur regs)))) by apply Eimg_env.
assert (Usp : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 2) = spZ (pi_regs D))
  by (rewrite (ps_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (HS : st_ok_pi segs VAL (Eimg (Ereg (pi_regs D) (ps_cur regs)))
  (mkSS (PS_OFF + PS_RET0) ps_sr_epi [ps_frame_region] None ps_facts_epi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PS_OFF + PS_RET0))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ps_frame_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    destruct HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    repeat apply Forall_cons; [..|apply Forall_nil].
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 1 1 eq_refl) S1 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 8 8 eq_refl) S2 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 9 9 eq_refl) S3 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 18 18 eq_refl) S4 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 19 19 eq_refl) S5 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 20 20 eq_refl) S6 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 21 21 eq_refl) S7 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 22 22 eq_refl) S8 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 23 23 eq_refl) S9 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 24 24 eq_refl) S10 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 25 25 eq_refl) S11 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 26 26 eq_refl) S12 HFR.
    + ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 27 27 eq_refl) S13 HFR.
  - exact (conj I I).
  - split; [|split; [exact I | exact I]]. cbn [ps_facts_epi f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia. }
assert (SHOK : sh_ok segs PS_Bx_epi [] (Eimg (Ereg (pi_regs D) (ps_cur regs))) (mrestrict (w_H W) mem))
  by (unfold sh_ok; apply Forall_nil).
remember (Eimg (Ereg (pi_regs D) (ps_cur regs))) as E eqn:HE.
clear HE HRO.
pose (RUN := @paj_run_x_invR fx rc SK _ PS_PAListing PS_PAImg B PST ARx _ LAWS P PLAW R Rr Rt).
pose (RET := @paj_ret_at fx rc _ PS_PAListing PS_PAImg).
unfold cfg_at, ps_pc, w64. replace (BASE + PS_OFF + PS_RET0) with (BASE + (PS_OFF + PS_RET0)) by lia.
paj_run_tok_x_invR RUN HS HJ SHOK HMN PS_Bspan;
  [cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = mem)
    by (apply functional_extensionality; intros x; apply HF; intros (r & Hin & Hr);
        cbn [ss_mem In] in Hin; destruct Hin as [<- | []];
        cbn [ps_frame_region YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; lia) end.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
(* the return step is the plain one: an SRr fact is an SRrG fact at every R containing wle *)
apply (SRr_SRrG segs R Rsub).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. rewrite Emem, R1, E1. rewrite Hra. rewrite Emem in HJ, HMN.
unfold ps_postPR.
eapply (YCbqGwild.fpostW_xb_of_keptR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) _
  (pi_regs D) _ _ _ _ _ _ _ [(pi_q D, pi_q D + 8)] [] ly S Hp W _ mem _ k WS).
- exact Hstk0.
- exact HBW.
- apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_depot S) WS);
    [| exact HWI].
  apply (ajournal_x_materializeR segs B PST ARx LAWS (@pa_segs_low _ _ PS_PAImg) R). exact HJ.
- apply (ps_kept_mdR R _ _ _ _ _ _ _ _ _ _ _ _ _ md); [exact HK|].
  eapply same_but_materialized_trans; apply same_but_materialized_wvb_any.
- intros a Ha. exact Ha.
- exact (aregs_preserved_of_st_ok segs _ _ _ _ (pi_regs D) (ps_cur regs) HS HAE ltac:(vm_compute; reflexivity)).
- split; [|exact HMN].
  exists 0. split; [rewrite R10; reflexivity|]. split; [exact HRL|].
  split; [exact HBB | apply ps_QresK_of_res; exact HQ].
Qed.
Theorem ps_ret0_walkP : ps_seg_ret0P B ARx SK P CTX CW.
Proof. exact (ps_ret0_walkPR (@wle segs) (wle_refl segs) (wle_trans segs) (fun W W' H => H)). Qed.

(* ---- the success tail's helpers: byte windows a two-store run leaves alone, and the shadow arithmetic (the
   S1 walk FuzzStrdup.v's sd_* lemmas, here at the RunCeil ceiling YM05.alloc_ceiling) ---- *)
Lemma ps_val_mem_keep : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v H HV k Hk. rewrite H by lia. exact (HV k Hk). Qed.
Lemma ps_garr8_keep : forall (m m' : word -> option byte) p l,
  (forall x, p <= x < p + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  garr8 segs m p l -> garr8 segs m' p l.
Proof.
intros m m' p l H HG j Hj. destruct (HG j Hj) as [HV Hb]. split; [|exact Hb].
apply (ps_val_mem_keep m m' _ 1 _); [|exact HV]. intros x Hx. apply H. cbn in Hx. lia.
Qed.
Lemma ps_forall_skipn : forall (Pz : Z -> Prop) n (l : list Z), Forall Pz l -> Forall Pz (skipn n l).
Proof.
intros Pz n. induction n as [|n IH]; intros l H; [exact H|].
destruct l as [|a l]; cbn; [constructor|]. apply IH. inversion H; assumption.
Qed.
Lemma ps_ro_img : forall a, in_roP segs (@pa_relro_lo _ A_prog_listing PS_PAImg) (@pa_relro_hi _ A_prog_listing PS_PAImg) a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PS_PAImg a Hr)].
Qed.
Lemma ps_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma ps_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (P2 : 0 <= (SHADOW_OFF + x / 8) / 8) by (apply Z.div_pos; unfold SHADOW_OFF; lia).
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
Lemma ps_shadow_out : forall p len x, in_app p len -> p + len <= YM05.alloc_ceiling -> p <= x < p + len ->
  ~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hc Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma ps_hull_out : forall p len x n s, in_app p len -> p + len <= YM05.alloc_ceiling -> p <= x -> 0 < n ->
  x + n <= p + len ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
intros p len x n s Happ Hc Hx Hn Hxn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(discriminate)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(reflexivity)) as M1.
assert (P3 : (x + n - 1) / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(discriminate)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(reflexivity)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.
(* the statics the ledger reads are image bytes (the base's PST_ok, the same hypothesis) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).

(* the harness head is at least a word (the kit's prh_head_wide, PRH_Base.v blob ef7c8ca98529): the success tail needs it,
   since at cf_head = 0 the block's head word IS the user's first word, the NUL store at w = out would overwrite it,
   and ps_Qres's success arm (the ledger's head value Q + 1 AND pj_cbytesR's NUL at out) would be contradictory (text
   "", Q = 0). Discharged at the preset instance by a Theorem Labs lane's preset_head_wide (CfParamsPreset.v:103). ret0 does not
   use it. *)
Hypothesis HW : prh_head_wide.

(* ---- STRETCH 2: the success tail, from PS_RETOK. ONE run from 1352 to the `ret` at 1348 (the epilogue at 1288 is
   run in the same symbolic state, the frame region carried along): the shadow check of w (token engine, discharged by
   the new block's prhReader_vis), the NUL store at w, the shadow check of q (zero: the real stack's shadow law),
   s4 + 1, the cursor store at q, j 1288, the epilogue. The post is ps_Qres's success arm at the written memory. ---- *)
Theorem ps_retok_walkP : ps_seg_retokP B ARx SK P CTX CW.
Proof.
intros D ly S Hp W regs mem md out w r Q HPRE HAT.
destruct HAT as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & HSH & HGT & HIN & HSCAN
  & Hsp & H18 & H19 & H20 & H8 & H9 & Hr & (s & Hdec & Hbytes & Hlen) & Hlow & Hhigh).
pose proof HPRE as ((HPX & HROD) & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & Hplt & Hq34 & HWIN & Hqlo & Hqhi & HRA24 & _).
pose proof HPX as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as CH0.
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_pres HJ) as Jpres.
pose proof HAL as (Hcnt & Hout4096 & Hout16 & HHp & Hab & HLED & HVIS & HRL & HRP & HBBal).
pose proof HIN0 as (HV0 & HV8 & HV16 & HRW & Hq8 & Htext0 & Htl & Hptext & Hlentb & Hgtb & Hqtext & Hd32).
(* the closing quote is inside the text, so the new cursor p + Q + 2 is too *)
assert (HQr : pi_p D + 1 + Z.of_nat Q < pi_text D + pi_len D).
{ destruct (PjGrammar.scan_quote _ _ HSCAN) as [HQlt _].
  unfold ps_x, rest_atR in HQlt. rewrite length_skipn in HQlt. lia. }
assert (HFR : PS_FRAME = 144) by (vm_compute; reflexivity).
(* DERIVED (vm_compute on the generated PRH_Img value): parse_string's stack budget covers its own frame *)
assert (HSTKge : 144 <= STK_parse_string) by (vm_compute; discriminate).
assert (Hinb : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & Hbpw).
assert (Hrq2 : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
assert (Hwb : out - cf_head <= w < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)) by lia.
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
assert (Hqstk : ly_stk_lo ly <= pi_q D /\ pi_q D + 8 <= ly_stk_hi ly).
{ destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _). rewrite Elo, Ehi. split; lia. }
assert (Hqsh : aview segs (w_H W) mem (SHADOW_OFF + pi_q D / 8) = Some 0)
  by (apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md); [exact HARc | lia]).
(* the register and value bounds *)
assert (Hqlo46 : 2 ^ 46 <= pi_q D) by lia.
assert (Hqhi47 : pi_q D + 24 <= 2 ^ 47) by lia.
assert (Hq64 : 0 <= pi_q D < 2 ^ 64) by lia.
assert (Hw4096 : 4096 <= w) by lia.
assert (Hw64 : 0 <= w < 2 ^ 64) by lia.
assert (Hwapp : app_addr w) by (eapply in_app_addr; [exact Hbapp | exact Hwb]).
(* the shadow of the caller's cursor word is zero at the current state *)
assert (HRAq : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (pi_q D) 8).
{ apply (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF (pi_q D) 8 Hq8 eq_refl).
  intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold shadow_of_addr. exact Hqsh. }
pose proof HVIS as (HRAout & HHULLout).
(* the environment *)
assert (E51 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 51) = w)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite H19; unfold w64; apply unsigned_lit_small; lia).
assert (E40 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 40) = pi_q D)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite H8; unfold w64; apply unsigned_lit_small; lia).
assert (E56 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 56) = SHADOW_OFF)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite (proj1 HSH); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E52 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 52) = r)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite H20; unfold w64; apply unsigned_lit_small; lia).
assert (E50 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 50) = out)
  by (rewrite ps_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth ps_cur map all_regs];
      rewrite H18; unfold w64; apply unsigned_lit_small; lia).
assert (Esp2 : bv_unsigned (ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 2) = spZ (pi_regs D))
  by (rewrite (ps_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg (pi_regs D) (ps_cur regs)))) by apply Eimg_env.
assert (HS1 : st_ok_pi segs VAL (Eimg (Ereg (pi_regs D) (ps_cur regs)))
  (mkSS (PS_OFF + PS_RETOK) ps_sr_retok [ps_w_region; ps_q_region; ps_frame_region] None ps_facts_retok)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PS_OFF + PS_RETOK))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply (ps_regs_ok_retok D regs); try assumption; lia.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [..|apply Forall_nil]; unfold region_ok, ps_w_region, ps_q_region, ps_frame_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E51. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable segs). apply Hbpres. lia.
    + rewrite E40. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable segs). apply Jpres. unfold PS_WSP, PS_WSTK. lia.
    + rewrite Esp2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct HSV as (SV1 & SV2 & SV3 & SV4 & SV5 & SV6 & SV7 & SV8 & SV9 & SV10 & SV11 & SV12 & SV13).
      repeat apply Forall_cons; [..|apply Forall_nil].
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 1 1 eq_refl) SV1 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 8 8 eq_refl) SV2 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 9 9 eq_refl) SV3 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 18 18 eq_refl) SV4 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 19 19 eq_refl) SV5 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 20 20 eq_refl) SV6 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 21 21 eq_refl) SV7 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 22 22 eq_refl) SV8 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 23 23 eq_refl) SV9 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 24 24 eq_refl) SV10 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 25 25 eq_refl) SV11 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 26 26 eq_refl) SV12 HFR.
      * ps_chunk (ps_ew_lo (pi_regs D) (ps_cur regs) 27 27 eq_refl) SV13 HFR.
  - apply pairwise_disjoint_of_extents.
    unfold ps_w_region, ps_q_region, ps_frame_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E51, E40, Esp2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [ps_facts_retok f_atoms atoms_ok].
    split; [|split; [|split; [|split; [|exact I]]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite E51. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite E40. change (2 ^ 3) with 8. lia.
    + rewrite E56. rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF. lia.
    + rewrite Esp2. change (2 ^ 4) with 16. lia. }
assert (SHOK1 : sh_ok segs PS_Bx_retok ps_SH_retok (Eimg (Ereg (pi_regs D) (ps_cur regs))) (mrestrict (w_H W) mem)).
{ repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (shent_ok_of_range segs (w_H W) mem _ PS_Bx_retok 51 out (Z.of_nat Q + 1) w 0 1 HRAout).
    + unfold U, PS_Bx_retok. cbn [sv_denot]. rewrite E56, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    + unfold U. cbn [sv_denot]. rewrite E51, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range segs (w_H W) mem _ PS_Bx_retok 40 (pi_q D) 8 (pi_q D) 0 8 HRAq).
    + unfold U, PS_Bx_retok. cbn [sv_denot]. rewrite E56, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    + unfold U. cbn [sv_denot]. rewrite E40, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia. }
assert (E1 : ew (Eimg (Ereg (pi_regs D) (ps_cur regs))) 1 = getr (pi_regs D) 1) by exact (ps_ew_lo _ _ 1 1 eq_refl).
assert (HAE : env_agree 32 (Ereg (pi_regs D) (ps_cur regs)) (Eimg (Ereg (pi_regs D) (ps_cur regs))))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* the charge of the one granted run: [EAlloc (S Q)], i.e. Q + 1 user bytes and one head *)
assert (Htr : PRH_Charge.prhPs_gtrace (ps_x D) = [PjGrammar.EAlloc (Datatypes.S Q)]).
{ unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. rewrite HSCAN, Hdec. reflexivity. }
assert (HTR : PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) = Z.of_nat Q + 1 + cf_head).
{ rewrite Htr. unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia. }
assert (HCH8 : 8 <= cf_head) by exact HW.
assert (Hsepw : forall b m x, In (b, m) (ablocks B ly S) -> (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head) ->
  b <= x < b + req_size m -> x <> w).
{ intros b m x Hbm Hne Hx Exw. subst x.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md b m _ _ HARc Hbm Hinb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
remember (Eimg (Ereg (pi_regs D) (ps_cur regs))) as E eqn:HE.
pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B PST ARx _ LAWS P PLAW).
pose (RET := @paj_ret_at fx rc _ PS_PAListing PS_PAImg).
unfold cfg_at, ps_pc, w64. replace (BASE + PS_OFF + PS_RETOK) with (BASE + (PS_OFF + PS_RETOK)) by lia.
paj_run_tok_x_inv RUN HS1 HJ SHOK1 HMN PS_Bspan.
+ cbn [ss_mem]. intros a (rg & Hin & Hrg). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [ps_w_region ps_q_region ps_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    rewrite ?E51, ?E40, ?Esp2 in Hrg.
  * right; right; left. exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
    split; [exact Hinb|]. split; [|lia]. exact (ps_newblk D ly S Hp W mem md out Q HAL HARc).
  * left. unfold PS_WSP, PS_WSTK. lia.
  * exfalso. lia.
+ (* ---- the final state, at the `ret`: the model after the run ---- *)
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m1 |} _ => remember m1 as md1 eqn:Emd1 end.
  assert (Hsbm : same_but_materialized md md1) by (rewrite Emd1; apply same_but_materialized_wvb_any).
  (* the two written words, read off the final symbolic state *)
  pose proof (st_ok_mem_ok segs _ _ _ HS1) as (_ & HRS & _).
  cbn [abs_ss setpc ss_mem restrict ms_mem] in HRS.
  apply Forall_cons_iff in HRS as (HRw & HRS). apply Forall_cons_iff in HRS as (HRq & _).
  destruct HRw as (_ & _ & _ & HCw). destruct HRq as (_ & _ & _ & HCq).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCw, HCq.
  rewrite !ew_ewset_other in HCw by lia. rewrite !ew_ewset_other in HCq by lia.
  rewrite E51 in HCw. rewrite E40 in HCq.
  pose proof (Forall_inv HCw) as HC0. pose proof (Forall_inv HCq) as HC1.
  assert (Hvw : val_mem segs (mrestrict (w_H W) (ms_mem ms)) w 1 0).
  { replace w with (w + 0) by lia.
    refine (val_of_chunk_ok segs _ _ w 0 1%N (SLit 0) 0 HC0 eq_refl _ _); cbn; lia. }
  assert (Hvq : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (pi_q D) 8 (r + 1)).
  { replace (pi_q D) with (pi_q D + 0) by lia.
    refine (val_of_chunk_ok segs _ _ (pi_q D) 0 8%N (SOff 52 1) (r + 1) HC1 _ _ _); [| cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E52. reflexivity. }
  (* every other byte is the pre-run one *)
  assert (Hkm : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 1) -> ~ (pi_q D <= a < pi_q D + 8) ->
    mbyte segs (mrestrict (w_H W) (ms_mem ms)) a = mbyte segs (mrestrict (w_H W) mem) a).
  { intros a Ha Hwa Hqa. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by lia. intros (rg & Hin & Hrg). cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [ps_w_region ps_q_region ps_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
      rewrite ?E51, ?E40, ?Esp2 in Hrg; lia. }
  assert (Hkv : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 1) -> ~ (pi_q D <= a < pi_q D + 8) ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hwa Hqa; unfold aview; rewrite (Hkm a Ha Hwa Hqa); reflexivity).
  (* the kept relation: the run's two writes (the new block's byte w, the caller's word FP), then from entry *)
  assert (HKx : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [(w, w + 1)]
      ly S W mem md ly S W (ms_mem ms) md1).
  { apply (cj_kept_exec SK segs B PST ARx _ LAWS (@pa_segs_low _ _ PS_PAImg) _ _ _ _ ly S Hp W mem md _ _
      (fun a => (w <= a < w + 1) \/ (pi_q D <= a < pi_q D + 8)) HARc).
    - rewrite Elo. exact Hceil.
    - rewrite Elo. lia.
    - rewrite Ehi. lia.
    - intros x Hx. apply HFr. intros (rg & Hin & Hrg). apply Hx. cbn [ss_mem In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]];
        cbn [ps_w_region ps_q_region ps_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
        rewrite ?E51, ?E40, ?Esp2 in Hrg; lia.
    - intros a [Ha|Ha].
      + right; right. split; [exists (w, w + 1); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb | lia].
      + right; left. exists (pi_q D, pi_q D + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    - exact Hsbm. }
  assert (HKf : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
      (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W (ms_mem ms) md1).
  { eapply (cj_kept_trans SK segs B PST ARx _ LAWS) with (FP1 := []) (FP2 := [(w, w + 1)]) (Hpc := pi_Hp D) (Hp2 := Hp);
      [exact HK | exact HKx | exact HAR0 | exact HARc | lia | lia | |].
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right; left.
      exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb|].
      split; [exact (ps_newblk D ly S Hp W mem md out Q HAL HARc) | lia]. }
  (* ---- ps_Qres's success arm at the written memory ---- *)
  assert (HVIS1 : prhReader_vis W (ms_mem ms) out (Z.of_nat Q + 1)).
  { split.
    - apply (range_addressable_agree (aview segs (w_H W) mem)); [|exact HRAout].
      intros x Hx. assert (Hx47 : 0 <= x < 2 ^ 47) by lia. pose proof (ps_shadow_low x Hx47) as Hs.
      assert (Hsw : ~ (out - cf_head <= shadow_of_addr SHADOW_OFF x < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)))
        by (apply (ps_shadow_out _ _ x Hbapp Hbceil); lia).
      apply Hkv; lia.
    - intros Hn0 s0 Hs0.
      assert (Hl : 0 <= s0 < 2 ^ 46) by (apply (ps_hull_low out (Z.of_nat Q + 1) s0); [lia | lia | lia | exact Hs0]).
      assert (Ho : ~ (out - cf_head <= s0 < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)))
        by (apply (ps_hull_out _ _ out (Z.of_nat Q + 1) s0 Hbapp Hbceil); [lia | lia | lia | exact Hs0]).
      rewrite Hkv by lia. exact (HHULLout Hn0 s0 Hs0). }
  assert (Hxbytes : Forall (fun b => 0 <= b < 256) (ps_x D)).
  { unfold ps_x, rest_atR. apply ps_forall_skipn. apply Forall_forall. intros c Hc.
    apply In_nth with (d := 0) in Hc as (j & Hj & <-). exact (proj2 (Hgtb j Hj)). }
  assert (HCB : pj_cbytesR segs (mrestrict (w_H W) (ms_mem ms)) out s).
  { split; [exact (PjGrammar.G1_4_bytes _ _ _ Hxbytes Hdec)|].
    unfold bytes_at in Hbytes.
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Nat.lt_ge_cases j (length s)) as [Hjs|Hjs].
    - rewrite app_nth1 by exact Hjs. destruct (Hbytes j Hjs) as [HV Hb]. split; [|exact Hb].
      eapply (ps_val_mem_keep _ _ _ 1 _); [|exact HV]. intros x Hx. cbn in Hx. apply Hkm; lia.
    - assert (Ej : j = length s) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      split; [|lia]. replace (out + Z.of_nat (length s)) with w by lia. exact Hvw. }
  assert (HLED1 : prh_ledger B ly S Hp W (ms_mem ms) ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D)).
  { (* through the base's named ledger helpers only (Batch 2 reshapes prh_glob) *)
    pose proof HLED as HG0; apply ps_led_glob in HG0. pose proof HLED as Hnd; apply ps_led_nodup in Hnd.
    pose proof HLED as Hfa; apply ps_led_blocks in Hfa. pose proof HLED as Hperm; apply ps_led_heads in Hperm.
    apply ps_led_mk; [| exact Hnd | | exact Hperm].
    - assert (Hst : forall a, Exists (in_zr a) PST ->
        mbyte segs (mrestrict (w_H W) (ms_mem ms)) a = mbyte segs (mrestrict (w_H W) mem) a).
      { intros a Ha. destruct (PST_ok a Ha) as [Hi _]. pose proof (@pa_segs_low _ _ PS_PAImg a Hi) as Hal.
        apply Hkm; [lia | | lia].
        intros Hwa. apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HARc Hinb); [lia | exact Hi]. }
      exact (ps_glob_keep_mb W W mem (ms_mem ms) _ _ _ _ _ _ _ Hst HG0).
    - apply Forall_forall. intros [a kk] Hin.
      pose proof (proj1 (Forall_forall _ _) Hfa (a, kk) Hin) as (Hk0 & Hab' & Hhp & Ha16 & Hhv). cbn [fst snd] in *.
      split; [exact Hk0|]. split; [exact Hab'|]. split; [exact Hhp|]. split; [exact Ha16|].
      destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hab') as (_ & Ha4096 & Haceil & _ & _ & _).
      assert (Hrqa : kk + cf_head <= req_size (kk + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      eapply (ps_val_mem_keep _ _ _ 8 _); [|exact Hhv]. intros x Hx. apply Hkm; [lia | | lia].
      destruct Hin as [Ea | Hin'].
      + injection Ea as <- <-. lia.
      + enough (x <> w) by lia. apply (Hsepw (a - cf_head) (kk + cf_head) x Hab'); [|lia].
        intros Ee. injection Ee as Ee1 _. cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hno Hnd0]. apply Hno.
        clear - Hin' Ee1. revert Hin'. induction (pi_Lam D) as [|[a0 k0] L IH]; intros Hin'; [destruct Hin'|].
        destruct Hin' as [Eh | Ht]; cbn [map fst];
          [injection Eh as Ea Ek; subst a0 k0; replace out with a by lia; constructor | constructor; exact (IH Ht)]. }
  assert (HPJ : pj_in_okR segs (mrestrict (w_H W) (ms_mem ms)) (pi_q D) (pi_text D) (pi_len D)
      (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D)).
  { pose proof HIN as (_ & HVc8 & HVc16 & _ & _ & _ & _ & _ & _ & Hgtbc & _ & _).
    split; [replace (pi_p D + Z.of_nat Q + 2) with (r + 1) by lia; exact Hvq|].
    split; [eapply (ps_val_mem_keep _ _ _ 8 _); [|exact HVc8]; intros x Hx; apply Hkm; lia|].
    split; [eapply (ps_val_mem_keep _ _ _ 4 _); [|exact HVc16]; intros x Hx; apply Hkm; lia|].
    split; [intros x Hx; apply (apresent_writable segs); eapply apresent_grows; [exact HG|];
            apply Jpres; unfold PS_WSP, PS_WSTK; lia|].
    split; [exact Hq8|]. split; [exact Htext0|]. split; [exact Htl|]. split; [lia|].
    split; [exact Hlentb|]. split; [|split; [exact Hqtext | exact Hd32]].
    eapply (ps_garr8_keep _ _ _ _); [|exact Hgtbc]. intros x Hx. rewrite Hlentb in Hx.
    apply Hkm; [lia | | lia].
    (* the text lies apart from the new block *)
    destruct HHOME as [[(b & m & Hbm & Hbt & Htb) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & Hnb & Hbt & Htb)].
    - pose proof HLED as Hnd; apply ps_led_nodup in Hnd. pose proof HLED as Hfa; apply ps_led_blocks in Hfa.
      pose proof (proj1 (Forall_forall _ _) Hfa (b, m) (or_intror Hbm)) as (Hm0 & Hab' & _ & _ & _).
      cbn [fst snd] in *.
      assert (Hrqb : m + cf_head <= req_size (m + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
      enough (x <> w) by lia. apply (Hsepw (b - cf_head) (m + cf_head) x Hab'); [|lia].
      intros Ee. injection Ee as Ee1 _. cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hno Hnd0]. apply Hno.
      clear - Hbm Ee1. revert Hbm. induction (pi_Lam D) as [|[a0 k0] L IH]; intros Hbm; [destruct Hbm|].
      destruct Hbm as [Eh | Ht]; cbn [map fst];
        [injection Eh as Ea Ek; subst a0 k0; replace out with b by lia; constructor | constructor; exact (IH Ht)].
    - enough (x <> w) by lia. intros Exw. subst x. destruct (Hro w Hx) as (Hri & _ & _).
      apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HARc Hinb); [lia | exact (ps_ro_img w Hri)].
    - enough (x <> w) by lia. intros Exw. subst x. destruct (Hro w Hx) as (Hri & _ & _).
      apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HARc Hinb); [lia | exact (ps_ro_img w Hri)].
    - assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      enough (x <> w) by lia. apply (Hsepw b m x Hbm); [|lia].
      intros Ee. injection Ee as Eb _. apply Hnb. rewrite HHp, Eb. left. reflexivity. }
  assert (HAE2 : env_agree 32 (Ereg (pi_regs D) (ps_cur regs)) (ewset (ewset E 512 w0) 513 w1))
    by (destruct HAE as [HA1 HA2]; split;
        [intros n Hn; rewrite !ew_ewset_other by lia; apply HA1; exact Hn | rewrite !ed_ewset; exact HA2]).
  (* ---- the return ---- *)
  prreg HS1 (10%bv : bv 5) R10. prreg HS1 (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS1 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite R1, E1, Hra.
  unfold ps_postP.
  (* the success path stores no wild trace: the post at budget [] (within any cursor set) *)
  eapply (YCbqGwild.fpostW_xb_of_kept (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) _
    (pi_regs D) _ _ _ _ _ _ _ [(pi_q D, pi_q D + 8)] [] ly S Hp W _ (ms_mem ms) _ k []).
  * exact Hstk0.
  * apply ps_wb_nil.
  * apply (ajournal_x_materialize segs B PST ARx LAWS (@pa_segs_low _ _ PS_PAImg)). exact HJ.
  * apply (ps_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HKf). apply same_but_materialized_wvb_any.
  * intros a Ha. exact Ha.
  * exact (aregs_preserved_of_st_ok segs _ _ _ _ (pi_regs D) (ps_cur regs) HS1 HAE2 ltac:(vm_compute; reflexivity)).
  * split; [|exact HMN].
    exists out. split; [rewrite R10; unfold w64; rewrite <- E50; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [exact HRL|]. split; [rewrite HTR; exact HBBal|].
    apply ps_QresK_of_res. unfold ps_Qres. rewrite HSCAN. right; right; right.
    split; [exact Hcnt|]. split; [exact Hout4096|]. split; [exact Hout16|].
    exists s, (rest_atR (pi_tb D) (pi_text D) (r + 1)). split; [exact Hdec|].
    split; [exact HHp|]. split; [exact Hab|]. split; [exact HVIS1|]. split; [exact HCB|].
    split; [exact HLED1|]. split; [exact HPJ|].
    (* the position transfer: the malloc's HMal event (ps_alloc's ps_rpos_mal) *)
    exact HRP.
Qed.

End pr.

(* ---- the stable statements, BYTE-IDENTICAL, as the P := (fun _ => True) instances ---- *)
Section prT. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
#[local] Notation PST := (prh_pst ).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Theorem ps_ret0_walk : ps_seg_ret0 B ARx SK CTX CW.
Proof. apply (proj1 (ps_seg_ret0_of_True B ARx SK CTX CW)). exact (ps_ret0_walkP B ARx SK CTX CW LAWS _ srr_inv_laws_True). Qed.
(* its form over R beside (the NULL return after the bad escape's fuzz_free) *)
Theorem ps_ret0_walkR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle segs W W' -> R W W') ->
  ps_seg_ret0R B ARx SK R CTX CW.
Proof.
intros R Rr Rt Rsub. apply (proj1 (ps_seg_ret0R_of_True B ARx SK R CTX CW)).
exact (ps_ret0_walkPR B ARx SK CTX CW LAWS _ srr_inv_laws_True R Rr Rt Rsub).
Qed.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HW : prh_head_wide.
Theorem ps_retok_walk : ps_seg_retok B ARx SK CTX CW.
Proof.
apply (proj1 (ps_seg_retok_of_True B ARx SK CTX CW)).
exact (ps_retok_walkP B ARx SK CTX CW LAWS _ srr_inv_laws_True PST_ok HW).
Qed.
End prT.
