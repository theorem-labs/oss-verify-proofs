(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1014 of its 1163 lines of code are new or changed and 2537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread.v, with its module paths and module names changed; 1341 of its 1416 lines of code are new or changed and 1088 lines of the source are left out. *)
(* check_no_overread 0x811c8 (fs.c), fs.asan: the TOP of the ASan walk of FSH_Fn_cno.v check_no_overread_spec.
   It chains segment 1 (FSW_check_no_overread.v cno_seg1), the sixteen call sites and the return, and states
   check_no_overread_ok. Each call site is one call step of the interface in FSW_check_no_overread.v (cno_site ->
   cno_ret); the code between two call sites is run by the engine (FSW_K fsw_aj_run_toU), and the symbolic state at
   each return is rebuilt by cno_after (FSW_check_no_overread_inv.v cno_resume). The chain is written backwards as
   segment lemmas from the next boundary to this one: `cno_from ss INV` at the returns of past_nul x2 / __wrap_malloc
   (the entry walk's fe_from form, FSW_entry_defs.v:133), `cno_at pc INV` (_inv.v) at the memset call (INV_MS), the
   first decode call (INV_D1) and the first fuzz_free call (INV_F1); every boundary is the state the segment before
   it produces (each is established by that segment, so none is assumed without a witness).
   Here: cno_enter (segment 1, past_nul #1), cno_seg_P1 (past_nul #2), cno_seg_P2 (__wrap_malloc), cno_seg_M (the
   copy), cno_seg_MS (the memset, the inline check, the stores), cno_chain; segment D (_segd.v, the decodes, the
   branches, bcmp x2) and segment F (_segf.v, fuzz_free x3, __wrap_free x3) and the lanes' call steps (_mem.v,
   _dec.v, _tail.v, _ffree.v, _ret.v) are applied as their real lemmas in check_no_overread_ok (Section F). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl
FSW_check_no_overread FSW_check_no_overread_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer ACem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_check_no_overread_mem FSW_check_no_overread_dec
  FSW_check_no_overread_tail FSW_check_no_overread_ret FSW_check_no_overread_ffree FSW_check_no_overread_segd
  FSW_check_no_overread_segf AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the boundary states ================= *)
(* the slot 0x18(s1) holds the first past_nul result (0x812fc), the walk's extra atom 48 *)
Definition cno_sl18 : list YP09.chunk := [YP09.mkChunk 24 (CVal 8 (SOff 48 0))].
Definition ss_P1 : sstate := cno_ss 0x812fc 19 18 cno_flag_chunk [].
Definition ss_P2 : sstate := cno_ss 0x81310 19 18 cno_flag_chunk cno_sl18.
(* the state after the memset (0x81358): the boundary's four regions; then the inline check's own: the byte
   t + len + 17 (s6, atom 22) that 0x81374 stores, the shadow byte of that granule (atom 52, its value atom 53), and
   the aliases the engine needs for `srli a0, s6, 3; add a0, a0, s9` (atom 51 = s6 >> 3, 52 = s9 + 51) and for
   `andi a1, s6, 7` (atom 54) *)
Definition ss_S0 : sstate := cno_ss 0x81358 19 18 cno_flag_chunk cno_sl10.
Definition cno_R22 : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 1 [].
Definition cno_R52 : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition cno_GS : facts := mkFacts ((53%nat, mkAF 0 7 0) :: f_atoms (ss_facts ss_S0)) []
  [(SAlu ALU_SRL (SOff 22 0) (SLit 3), SOff 51 0); (SAlu ALU_ADD (SOff 51 0) (SOff 25 0), SOff 52 0);
   (SAlu ALU_AND (SOff 22 0) (SLit 7), SOff 54 0)].
Definition ss_S : sstate :=
  set_facts (mkSS (ss_pc ss_S0) (ss_regs ss_S0) (ss_mem ss_S0 ++ [cno_R22; cno_R52]) (ss_resv ss_S0) (ss_facts ss_S0))
    cno_GS.

(* the state at the first decode call, on every path of the check (conditions dropped) *)
Definition cno_ssD : sstate := Eval vm_compute in
  (let r := fst (sym_run_toN tfibsegs cno_tbl FUEL A_preset_base64_decode
     (add_cond (fst (sym_runN tfibsegs cno_tbl FUEL ss_S)) (mkAC BC_EQ (SOff 53 0) (SLit 0)))) in
   set_facts r (mkFacts (f_atoms (ss_facts r)) [] (f_alias (ss_facts r)))).
(* drop a state's conditions *)
Ltac cno_dropc HS HSd :=
  lazymatch type of HS with st_ok ?sg ?E ?ss ?m =>
    pose proof (ACem.st_ok_facts_incl3 sg E ss m (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)) HS
      (fun x h => h) (fun x h => match h with end) (fun x h => h)) as HSd;
    let Eq := fresh "Eq" in
    assert (Eq : set_facts ss (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))) = cno_ssD)
      by (vm_compute; reflexivity);
    rewrite Eq in HSd; clear Eq
  end.

(* a byte the view reads, as a one-byte val_mem *)
Lemma cno_vm1 : forall H (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia). replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a present byte is writable *)
Lemma cno_apw : forall H (m : word -> option byte) a, apresent H m a -> writable_at tfibsegs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* an entry of a pairwise-disjoint block list occurs once *)
Lemma cno_fresh : forall (l1 l2 : list (Z * Z)) x,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (l1 ++ l2)) -> In x l2 -> 1 <= req_size (snd x) ->
  ~ In x l1.
Proof.
intros l1 l2 x. induction l1 as [|y l1 IH]; intros HP Hx Hr Hin; [destruct Hin|].
cbn [app map pairwise] in HP. destruct HP as [HF HP].
destruct Hin as [<- | Hin]; [|exact (IH HP Hx Hr Hin)].
assert (Hx' : In (fst y, req_size (snd y)) (map (fun b => (fst b, req_size (snd b))) (l1 ++ l2))).
{ apply (in_map (fun b => (fst b, req_size (snd b))) (l1 ++ l2) y). apply in_or_app. right. exact Hx. }
pose proof (proj1 (Forall_forall _ _) HF _ Hx') as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* the env past the boundary atoms grows without changing a state that reads only atoms below 51 *)
Lemma cno_st_lift {fx : YK11.FPState} : forall cx A Bp T extra (W : world tfibsegs) regs ss ms,
  st_ok tfibsegs (Ereg regs (cno_xs cx A Bp T [])) ss (restrict (w_H W) ms) -> ss_atoms_lt 51 ss = true ->
  st_ok tfibsegs (Ereg regs (cno_xs cx A Bp T extra)) ss (restrict (w_H W) ms).
Proof.
intros cx A Bp T extra W regs ss ms HS Hat. apply (st_ok_agree tfibsegs 51 _ _ ss _ HS); [|exact Hat].
split; [|reflexivity]. intros n Hn. unfold Ereg. cbn [ew].
destruct (n <? 32)%nat eqn:E; [reflexivity|]. apply Nat.ltb_ge in E.
unfold cno_xs. rewrite app_nil_r, app_assoc. apply app_nth1. cbn [length fs_extraT cno_extra app]. lia.
Qed.
(* regions appended to a state (restated from lib/A/AD25.v:21, which this walk does not load) *)
Lemma cno_app_regions {fx : YK11.FPState} : forall E ss ms rs',
  st_ok tfibsegs E ss ms -> regions_wf rs' = true -> Forall (region_ok tfibsegs E (ms_mem ms)) rs' ->
  pairwise_disjoint E rs' -> (forall r1 r2, In r1 (ss_mem ss) -> In r2 rs' -> extent_disjoint E r1 r2) ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwf' Hok' Hpd' Hx.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9]. split; [| split].
- clear -Hwf Hwf'. induction (ss_mem ss) as [|r rs IH]; cbn in *; [exact Hwf'|]. apply andb_prop in Hwf as [Ha Hb].
  rewrite Ha, (IH Hb). reflexivity.
- apply Forall_app. split; assumption.
- apply YP08.pairwise_disjoint_app; assumption.
Qed.
(* the inline check's state: ss_S0 plus the stored byte x = t + len + 17 (atom 22), the shadow byte of x's granule
   (address atom 52 = SHADOW_OFF + x / 8, value atom 53), the aliases *)
Lemma cno_ssS_ok {fx : YK11.FPState} {rc : YM05.RunCeil} : forall cx A Bp T x s (W : world tfibsegs) ms,
  st_ok tfibsegs (Ereg (ms_regs ms) (cno_xs cx A Bp T [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]))
    ss_S0 (restrict (w_H W) ms) ->
  getr (ms_regs ms) 22 = w64 x -> getr (ms_regs ms) 25 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 47 -> 0 <= s <= 7 ->
  writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) x ->
  aview tfibsegs (w_H W) (ms_mem ms) (SHADOW_OFF + x / 8) = Some s ->
  (forall r, In r (ss_mem ss_S0) ->
     extent_disjoint (Ereg (ms_regs ms) (cno_xs cx A Bp T [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]))
       r cno_R22 /\
     extent_disjoint (Ereg (ms_regs ms) (cno_xs cx A Bp T [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]))
       r cno_R52) ->
  x + 1 <= SHADOW_OFF + x / 8 \/ SHADOW_OFF + x / 8 + 1 <= x ->
  st_ok tfibsegs (Ereg (ms_regs ms) (cno_xs cx A Bp T [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]))
    ss_S (restrict (w_H W) ms).
Proof.
intros cx A Bp T x s W ms HS R22 R25 Hx Hs Hw Hv Hdis Hd2.
set (E := Ereg (ms_regs ms) (cno_xs cx A Bp T [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)])) in *.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (Hsh : 0 <= SHADOW_OFF + x / 8 < 2 ^ 47) by (unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (E22 : ew E 22 = w64 x) by (subst E; rewrite (ew_Ereg_nat _ _ 22 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = w64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat _ _ 25 25%bv eq_refl); exact R25).
assert (E51 : ew E 51 = w64 (x / 8)) by (subst E; change 51%nat with (32 + 19)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E52 : ew E 52 = w64 (SHADOW_OFF + x / 8))
  by (subst E; change 52%nat with (32 + 20)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E53 : ew E 53 = w64 s) by (subst E; change 53%nat with (32 + 21)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E54 : ew E 54 = w64 (x mod 8)) by (subst E; change 54%nat with (32 + 22)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U22 : bv_unsigned (ew E 22) = x) by (rewrite E22; unfold w64; apply wz; lia).
assert (U52 : bv_unsigned (ew E 52) = SHADOW_OFF + x / 8) by (rewrite E52; unfold w64; apply wz; lia).
unfold ss_S. apply st_ok_set_facts.
- apply (cno_app_regions E ss_S0 _ [cno_R22; cno_R52] HS).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, cno_R22. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. cbn [ms_mem restrict]. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (x + o) with x by lia. exact Hw.
    * unfold region_ok, cno_R52. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U52. cbn [ms_mem restrict]. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ _ 0 1%N (SOff 53 0) s); [rewrite fsw_SOff0, E53; reflexivity | cbn; lia | cbn; lia|].
      rewrite Z.add_0_r. exact (cno_vm1 _ _ _ _ Hv).
  + cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, cno_R22, cno_R52. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U22, U52. lia.
  + intros r1 r2 Hr1 Hr2. destruct (Hdis r1 Hr1) as (D1 & D2).
    destruct Hr2 as [<- | [<- | []]]; assumption.
- pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & HC & HL)).
  split; [|split; [exact I|]].
  + cbn [f_atoms cno_GS atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E53. unfold w64. rewrite wz by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  + cbn [f_alias cno_GS alias_ok]. split; [|split; [|split; [|exact I]]].
    * apply U_inj. rewrite U_srl3, (U_atom E 22 x E22 ltac:(lia)), (U_atom E 51 (x / 8) E51) by (Z.div_mod_to_equations; lia).
      reflexivity.
    * apply U_inj. rewrite U_SAlu, (U_atom E 51 (x / 8) E51), (U_atom E 25 SHADOW_OFF E25),
        (U_atom E 52 (SHADOW_OFF + x / 8) E52) by (unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
      cbn [zalu_raw]. rewrite (Z.add_comm (x / 8) SHADOW_OFF). apply zcanon_id. unfold M64, SHADOW_OFF in *. lia.
    * apply U_inj. rewrite U_SAlu, U_SLit, (U_atom E 22 x E22 ltac:(lia)), (U_atom E 54 (x mod 8) E54)
        by (Z.div_mod_to_equations; lia).
      cbn [zalu_raw]. change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
      apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.


(* the regions of the state at the first decode call *)
Definition cno_rD (i : nat) : YP09.region :=
  match nth_error (ss_mem cno_ssD) i with Some r => r | None => YP09.mkRegion None 0 0 0 0 [] end.
Lemma cno_val_at {fx : YK11.FPState} : forall E ss H ms i r n od (w : N) e v,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  In (YP09.mkChunk od (CVal w e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E n) + od) (N.to_nat w) v.
Proof.
intros E ss H ms i r n od w e v HS Hi Hb Hc He Hv Hw.
exact (val_of_chunk_ok tfibsegs E _ _ od w e v (cno_chunk_at E ss H ms i r n _ HS Hi Hb Hc) He Hv Hw).
Qed.
(* a one-byte val_mem carried by an equal view *)
Lemma cno_vm1_kept : forall H H' (m m' : word -> option byte) a v,
  aview tfibsegs H' m' a = aview tfibsegs H m a -> val_mem tfibsegs (mrestrict H m) a 1 v ->
  val_mem tfibsegs (mrestrict H' m') a 1 v.
Proof.
intros H H' m m' a v E Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
rewrite (mbyte_of_aview tfibsegs H H' m m' a E). specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. exact Hv.
Qed.
Ltac cno_inc := vm_compute; repeat first [left; reflexivity | right].

Lemma cno_reg_add {fx : YK11.FPState} : forall H E ss ms (r : bv 5) n1 c1 n2 c2 v1 v2,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SAlu ALU_ADD (SOff n1 c1) (SOff n2 c2) ->
  ew E n1 = w64 v1 -> ew E n2 = w64 v2 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 + c1 < 2 ^ 64 ->
  0 <= v2 + c2 < 2 ^ 64 -> 0 <= v1 + c1 + (v2 + c2) < 2 ^ 64 ->
  getr (ms_regs ms) r = w64 (v1 + c1 + (v2 + c2)).
Proof.
intros H E ss ms r n1 c1 n2 c2 v1 v2 HS Hr E1 E2 R1 R2 R3 R4 R5.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply bv_eq.
change (U E (SAlu ALU_ADD (SOff n1 c1) (SOff n2 c2)) = bv_unsigned (w64 (v1 + c1 + (v2 + c2)))).
rewrite U_SAlu, (U_atom_off E n1 v1 c1 E1 R1 R3), (U_atom_off E n2 v2 c2 E2 R2 R4). cbn [zalu_raw].
unfold w64. rewrite wz by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* ================= the chain ================= *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* past_nul's contract (CTX-free since the owner's CTX drop, 05:05Z) *)
Hypothesis PN : past_nul_spec tfibsegs B.
(* segment 1's (FSW_check_no_overread.v Section W) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1.
Hypothesis ASM1 : astack_malloc_realizesU tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* the lanes' call steps, exactly the interface's Props (FSW_check_no_overread.v Section I, CTX-free) *)
Hypothesis cno_call_mal : cno_call_mal_T B.
Hypothesis cno_call_mcpy : cno_call_mcpy_T B.
Hypothesis cno_call_mset : cno_call_mset_T B.
Hypothesis cno_call_dec : cno_call_dec_T B.
Hypothesis cno_call_bcmp : cno_call_bcmp_T B.
Hypothesis cno_call_ffree : cno_call_ffree_T B.
Hypothesis cno_call_afree : cno_call_afree_T B.
Hypothesis cno_tail_ret : cno_tail_ret_T B.

(* ---- P1: the return of the first past_nul (0x812fc): a = past_nul (d, len, 'A') in a0, nothing else changed ---- *)
Definition INV_P1 : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a,
  U3 = c_U cx /\ k = 1 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18)] /\
  a <> 0 /\ a mod 16 = 0 /\ cno_core cx E /\ ew E 10 = w64 a /\
  ew E 22 = w64 (cno_n cx) /\ ew E 23 = w64 (c_d cx) /\ ew E 25 = w64 SHADOW_OFF /\ ew E 26 = w64 (cno_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  FSupoisonU.fs_heads B ly3 S3 U3.

(* ---- the entry: segment 1, the first past_nul call (0x812f8), the return P1 ---- *)
Lemma cno_enter : cno_from B ss_P1 INV_P1 -> check_no_overread_spec tfibsegs B.
Proof.
intros HNX ly S U W regs mem md ch d db live peak cnt fail HPRE Hh Hfr Htop Hd Hn Hsrc Hnz Hblk Hmax Hg Hq
  Hhd Hnev Hbb.
pose proof HPRE as (HAPU & HRO).
apply (cno_seg1 B IMG HGOT HCELL HGUAR HUCELL HSM1 ASM1 SMP FS_ENV ML ly S U W regs mem md ch _ HAPU HRO Hfr).
cbv zeta. intros S2 pos regs2 md2 ms mat HS HJ HARU Hin Hfrs Eab Hnev2 Hbb2 HR2 HLG.
set (cx := mkCNOCX ly S U W regs mem md ch d db live peak cnt fail pos).
assert (Hb : cno_base B cx)
  by exact (conj HPRE (conj Hh (conj Hfr (conj Htop (conj Hd (conj Hn (conj Hsrc (conj Hnz (conj Hblk
    (conj Hmax (conj Hg (conj Hq (conj Hhd (conj Hnev Hbb)))))))))))))).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
destruct HR2 as (G2 & G9 & G8 & G3 & G4 & G10 & G22 & G23 & G25).
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
change (st_ok tfibsegs (cno_env cx regs2 0 0 0) cno_ssC (restrict (w_H W) ms)) in HS.
set (E := cno_env cx regs2 0 0 0) in *.
assert (HE : cno_E cx E) by apply cno_E_env.
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms) md2' HARU) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U (ms_mem ms)) md2' 1 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
change (frame_addr ly 1 pos) with (cno_F cx) in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (E8 : bv_unsigned (ew E 8) = cno_sp0 cx)
  by (subst E; unfold cno_env; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8; apply wz; unfold cno_sp0 in *; lia).
(* the registers at the call, read off cno_ssC *)
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl), G2;
      reflexivity).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl), G9;
      reflexivity).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl), G8;
      reflexivity).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl), G3;
      reflexivity).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl), G4;
      reflexivity).
assert (R1 : getr (ms_regs ms) 1 = w64 0x812fc)
  by exact (fsw_reg_lit (w_H W) E cno_ssC ms 1%bv 0x812fc HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 (c_d cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 10%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl), G23;
      exact Hd).
assert (R11 : getr (ms_regs ms) 11 = w64 (cno_n cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 11%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl), G22;
      exact Hn).
assert (R12 : getr (ms_regs ms) 12 = w64 65)
  by exact (fsw_reg_lit (w_H W) E cno_ssC ms 12%bv 65 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by exact (fsw_reg_extra (w_H W) regs2 _ cno_ssC ms 18%bv 15 HS ltac:(vm_compute; reflexivity)).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 19%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), G10;
      reflexivity).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 22%bv 22%bv 22 HS ltac:(vm_compute; reflexivity) eq_refl), G22;
      exact Hn).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl), G23;
      exact Hd).
assert (R25 : getr (ms_regs ms) 25 = w64 SHADOW_OFF)
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 25%bv 25%bv 25 HS ltac:(vm_compute; reflexivity) eq_refl), G25;
      reflexivity).
assert (R26 : getr (ms_regs ms) 26 = w64 (cno_F cx))
  by (rewrite (fsw_reg_atom (w_H W) regs2 _ cno_ssC ms 26%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), G10;
      reflexivity).
assert (Hh2 : FSupoisonU.fs_heads B ly S2 U) by exact (cno_heads B ly S ly S2 U Eab Hh).
assert (Hsite : cno_site B cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2')
  by exact (cno_site_of B cx E cno_ssC W ms 0 ly S2 U md2' 0x812fc HE E8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh2 R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
destruct (cno_src_kept B cx 0 ly S2 W (ms_mem ms) md2' Hb HJ HARU) as (Hsrc2 & Hblk2).
assert (Hg2 : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail)
  by exact (cno_glob_ledger W W mem (ms_mem ms) _ _ _ _ HLG Hg).
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E cno_ssC ms HS eq_refl).
replace (ss_pc cno_ssC) with A_past_nul by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_past_nul) (ms_mem ms) (seg_rom tfibsegs)) md2')
  with (cfg_at tfibsegs A_past_nul (ms_regs ms) (ms_mem ms) md2').
assert (Hq1 : quiet cnt fail 1) by (unfold quiet in *; lia).
assert (Hk1 : 0 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S2 + (cno_n cx + 18) <= LIVE_MAX).
{ rewrite Hbb2. change (cno_n cx) with (Z.of_nat (length db)).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES in *. lia. }
eapply SRr_bind.
{ exact (cno_call_pn B PN cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2' 65 live peak cnt fail
    Hb Hsite (or_introl R1) R10 R11 R12 ltac:(lia) Hsrc2 Hblk2 Hg2 Hq1 Hk1 Hbb1). }
cbv beta. intros W' c' _ (res & Hret).
(* the frame's flag chunk at the call (the frame region of cno_ssC, base atom 10 = F) *)
pose (r1 := match nth_error (ss_mem cno_ssC) 1 with Some r => r | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (Hr1 : nth_error (ss_mem cno_ssC) 1 = Some r1) by (vm_compute; reflexivity).
assert (Hrb1 : YP09.r_base r1 = Some 10%nat) by (vm_compute; reflexivity).
assert (Hrc1 : In (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) (YP09.r_chunks r1))
  by (vm_compute; right; right; right; left; reflexivity).
pose proof (fsw_region_nth _ _ _ 1 _ HS Hr1) as HR1. cbn [ms_mem restrict] in HR1.
destruct HR1 as (_ & _ & _ & Hcs1). rewrite Hrb1 in Hcs1. cbn [base_val] in Hcs1.
assert (E10 : bv_unsigned (ew E 10) = cno_F cx)
  by (subst E; unfold cno_env; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), G10; apply wz; exact HF64).
rewrite E10 in Hcs1.
pose proof (proj1 (Forall_forall _ _) Hcs1 _ Hrc1) as Hflag.
destruct (cno_resume B cx 0 ly S2 U W (ms_regs ms) (ms_mem ms) md2' 1 U (fun _ => False) _ W' c'
  (fs_extraT ++ cno_extra regs (cno_FL cx) (cno_SF cx) res 0 0) cno_flag_chunk [] Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros a _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E cno_ssC W ms HE E8 HS ltac:(vm_compute; reflexivity)))).
  intros j Hj. exact (cno_env_saved cx regs2 regs' 0 0 0 res 0 0 j Hj).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- apply Forall_nil.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ Hflag). rewrite !fsw_SOff0. unfold cno_env.
  change 46%nat with (32 + 14)%nat. rewrite !ew_Ereg_extra. reflexivity.
- intros regs' _. apply Forall_nil.
- cbv beta in HPP. destruct HPP as (E10' & Hres0 & Hres16 & Hab & Hz & Hg').
  assert (Era : raZ (ms_regs ms) = 0x812fc) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' (fs_extraT ++ cno_extra regs (cno_FL cx) (cno_SF cx) res 0 0)) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  apply (HNX cx E' (0 + 1) ly' S' U W' (mkst regs' (Z_to_bv 64 0x812fc) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' res 0 0) HJ' HARU').
  + exists res. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab, Eab; reflexivity|].
    split; [exact Hres0|]. split; [exact Hres16|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)), (KR 19%bv 19%nat eq_refl ltac:(cno_cs)),
      (KR 3%bv 3%nat eq_refl ltac:(cno_cs)), (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split; [rewrite (KR 26%bv 26%nat eq_refl ltac:(cno_cs)); exact R26|].
    split; [exact Hz|]. split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* ---- P2: the return of the second past_nul (0x81310): b = past_nul (d, len, 'B') in a0, a in the slot 0x18(s1) ---- *)
Definition INV_P2 : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b,
  U3 = c_U cx /\ k = 2 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18); (b, cno_n cx + 18)] /\
  a <> 0 /\ a mod 16 = 0 /\ b <> 0 /\ b mod 16 = 0 /\ cno_core cx E /\ ew E 48 = w64 a /\ ew E 10 = w64 b /\
  ew E 22 = w64 (cno_n cx) /\ ew E 23 = w64 (c_d cx) /\ ew E 25 = w64 SHADOW_OFF /\ ew E 26 = w64 (cno_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) b (pn_copy (c_db cx) 66) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  FSupoisonU.fs_heads B ly3 S3 U3.

(* ---- from P1: the store of a at 0x812fc, the second past_nul call (0x8130c), the return P2 ---- *)
Lemma cno_seg_P1 : cno_from B ss_P2 INV_P2 -> cno_from B ss_P1 INV_P1.
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & -> & -> & Hab & Ha0 & Ha16 & (C2 & C8 & C9 & C18 & C19 & C3 & C4) & E10 & E22 & E23 & E25 & E26
  & Hz & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnevj & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly3 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite <- EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite C19; unfold w64; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
(* the run 0x812fc -> 0x82728 (the slot 0x18(s1) := a, a0 := d, a1 := len, a2 := 'B', ra := 0x81310) *)
fsw_aj_run_toU cno_tbl_ok HS HJ HARU A_past_nul.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x812fc cno_flag_chunk [] ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
(* the call site *)
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity)); exact C2).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (cno_reg _ E _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact C8).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 9%bv 9 HS ltac:(vm_compute; reflexivity)); exact C9).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (cno_reg _ E _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity)); exact C3).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (cno_reg _ E _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity)); exact C4).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by (rewrite (cno_reg _ E _ ms 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact C18).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity)); exact C19).
assert (R10 : getr (ms_regs ms) 10 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 10%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R11 : getr (ms_regs ms) 11 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 11%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 22%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 23%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R25 : getr (ms_regs ms) 25 = w64 SHADOW_OFF)
  by (rewrite (cno_reg _ E _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (R26 : getr (ms_regs ms) 26 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 26%bv 26 HS ltac:(vm_compute; reflexivity)); exact E26).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81310)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x81310 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R12 : getr (ms_regs ms) 12 = w64 66)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 12%bv 66 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Hsite : cno_site B cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4)
  by exact (cno_site_of B cx E ssR W3 ms 1 ly3 S3 (c_U cx) md4 0x81310 HE U8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
destruct (cno_src_kept B cx 1 ly3 S3 W3 (ms_mem ms) md4 Hb HJ HARU) as (Hsrc2 & Hblk2).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
{ apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
  intros x Hx. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) x (KL x Hx)). }
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hza : zbytes_at tfibsegs W3 (ms_mem ms) a (pn_copy (c_db cx) 65)).
{ apply (cno_zbytes_kept W3 W3 (ms_mem ms3) (ms_mem ms) a _); [|exact Hz].
  intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj. fold (cno_n cx) in Hj.
  pose proof (req_size_pos (cno_n cx + 18) ltac:(unfold cno_n; lia)) as Hrq.
  exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (a + j) (KB a (cno_n cx + 18) j HaIn ltac:(lia))). }
assert (Hq1 : quiet (c_cnt cx) (c_fail cx) 1).
{ pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & _). unfold quiet in *. lia. }
assert (Hk1 : 1 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S3 + (cno_n cx + 18) <= LIVE_MAX).
{ pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & _ & _ & _ & Hbb0).
  rewrite (blocks_bytes_bsum B ly3 S3), Hab, cno_bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  change (bsum [(a, cno_n cx + 18)]) with (cno_n cx + 18 + 0).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES, cno_n in *. lia. }
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with A_past_nul by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_past_nul) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs A_past_nul (ms_regs ms) (ms_mem ms) md4).
eapply SRr_bind.
{ exact (cno_call_pn B PN cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 66 (c_live cx) (c_peak cx) (c_cnt cx)
    (c_fail cx) Hb Hsite (or_intror R1) R10 R11 R12 ltac:(lia) Hsrc2 Hblk2 Hg2 Hq1 Hk1 Hbb1). }
cbv beta. intros W' c' _ (res & Hret).
(* the chunks at the call: the flag word (frame region 1, base 19) and a in the slot 0x18(s1) (slot region 3, base 9) *)
pose (rF := match nth_error (ss_mem ssR) 1 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 120 (CVal 8 (SOff 46 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 1 rF 19 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  vm_compute. left. reflexivity. }
pose (rL := match nth_error (ss_mem ssR) 3 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 24 (CVal 8 (SOff 10 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 3 rL 9 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  vm_compute. left. reflexivity. }
rewrite U19 in HcF. rewrite U9 in HcL.
destruct HE as (HE32 & HE33 & HE46 & HE47).
set (xs := fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a res 0).
destruct (cno_resume B cx 1 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 1 (c_U cx) (fun _ => False) _ W' c' xs
  cno_flag_chunk cno_sl18 Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros x _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E ssR W3 ms (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS
    ltac:(vm_compute; reflexivity)))).
  intros j Hj. destruct (cno_E_env cx regs' a res 0) as (_ & HX & _). exact (eq_trans (HX j Hj) (eq_sym (HE33 j Hj))).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcF). rewrite !fsw_SOff0.
  destruct (cno_E_env cx regs' a res 0) as (_ & _ & X46 & _). exact (eq_trans X46 (eq_sym HE46)).
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E10.
  unfold xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbv beta in HPP. destruct HPP as (E10' & Hres0 & Hres16 & Hab' & Hzr & Hg').
  assert (Era : raZ (ms_regs ms) = 0x81310) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' xs) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  apply (HNX cx E' (1 + 1) ly' S' (c_U cx) W' (mkst regs' (Z_to_bv 64 0x81310) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' a res 0) HJ' HARU').
  + exists a, res. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab', Hab, <- app_assoc; reflexivity|].
    split; [exact Ha0|]. split; [exact Ha16|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
      (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
      (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; unfold xs; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split; [rewrite (KR 26%bv 26%nat eq_refl ltac:(cno_cs)); exact R26|].
    split.
    { apply (cno_zbytes_kept W3 W' (ms_mem ms) mem' a _); [|exact Hza].
      intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj. fold (cno_n cx) in Hj.
      pose proof (req_size_pos (cno_n cx + 18) ltac:(unfold cno_n; lia)) as Hrq.
      apply (HBK a (cno_n cx + 18) j HaIn); [rewrite Hab'; apply in_or_app; left; exact HaIn | lia | intros X; exact X]. }
    split; [exact Hzr|]. split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* ---- M: the return of __wrap_malloc (len + 18) (0x81320): t in a0, b in s4, len + 18 in s8 ---- *)
Definition ss_M : sstate := cno_ss 0x81320 19 18 cno_flag_chunk cno_sl18.
Definition INV_M : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b t,
  U3 = c_U cx /\ k = 3 /\
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18); (b, cno_n cx + 18); (t, cno_n cx + 18)] /\
  a <> 0 /\ a mod 16 = 0 /\ b <> 0 /\ b mod 16 = 0 /\ t <> 0 /\ cno_core cx E /\
  ew E 48 = w64 a /\ ew E 49 = w64 b /\ ew E 50 = w64 t /\ ew E 10 = w64 t /\ ew E 20 = w64 b /\
  ew E 22 = w64 (cno_n cx) /\ ew E 23 = w64 (c_d cx) /\ ew E 24 = w64 (cno_n cx + 18) /\
  ew E 25 = w64 SHADOW_OFF /\ ew E 26 = w64 (cno_F cx) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) b (pn_copy (c_db cx) 66) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) /\
  FSupoisonU.fs_heads B ly3 S3 U3.

(* ---- from P2: s4 := b, s8 := len + 18, the __wrap_malloc call (0x8131c), the return M ---- *)
Lemma cno_seg_P2 : cno_from B ss_M INV_M -> cno_from B ss_P2 INV_P2.
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & -> & -> & Hab & Ha0 & Ha16 & Hb0 & Hb16 & (C2 & C8 & C9 & C18 & C19 & C3 & C4) & E48 & E10
  & E22 & E23 & E25 & E26 & Hza0 & Hzb0 & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & Hq & _ & _ & Hbb0).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnevj & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly3 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite <- EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx)
  by (rewrite C19; unfold w64; apply wz; unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
assert (Hn64 : 0 <= cno_n cx + 18 < 2 ^ 64) by (unfold cno_n, PRESET_FILE_MAX_BYTES in *; lia).
assert (Hn0 : 0 <= cno_n cx < 2 ^ 64) by (unfold cno_n, PRESET_FILE_MAX_BYTES in *; lia).
(* the run 0x81310 -> 0x53074 (s4 := b, s8 := a0 := len + 18, ra := 0x81320) *)
fsw_aj_run_toU cno_tbl_ok HS HJ HARU PC_malloc.
{ eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); lia. }
destruct (cno_run_keeps B cx E 0x81310 cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms) _ (ms_mem ms3) (ms_mem ms)
  Hb HARU Hin EF U8 U9 U19 U18 HF) as (KL & KB).
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HS with st_ok _ _ ?ss _ => set (ssR := ss) in HS end.
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 2%bv 2 HS ltac:(vm_compute; reflexivity)); exact C2).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (cno_reg _ E _ ms 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact C8).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg _ E _ ms 9%bv 9 HS ltac:(vm_compute; reflexivity)); exact C9).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (cno_reg _ E _ ms 3%bv 3 HS ltac:(vm_compute; reflexivity)); exact C3).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (cno_reg _ E _ ms 4%bv 4 HS ltac:(vm_compute; reflexivity)); exact C4).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by (rewrite (cno_reg _ E _ ms 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact C18).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 19%bv 19 HS ltac:(vm_compute; reflexivity)); exact C19).
assert (R10 : getr (ms_regs ms) 10 = w64 (cno_n cx + 18))
  by exact (cno_reg_off _ E _ ms 10%bv 22 18 (cno_n cx) HS ltac:(vm_compute; reflexivity) E22 Hn0 Hn64).
assert (R20 : getr (ms_regs ms) 20 = w64 b)
  by (rewrite (cno_reg _ E _ ms 20%bv 10 HS ltac:(vm_compute; reflexivity)); exact E10).
assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
  by (rewrite (cno_reg _ E _ ms 22%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R23 : getr (ms_regs ms) 23 = w64 (c_d cx))
  by (rewrite (cno_reg _ E _ ms 23%bv 23 HS ltac:(vm_compute; reflexivity)); exact E23).
assert (R24 : getr (ms_regs ms) 24 = w64 (cno_n cx + 18))
  by exact (cno_reg_off _ E _ ms 24%bv 22 18 (cno_n cx) HS ltac:(vm_compute; reflexivity) E22 Hn0 Hn64).
assert (R25 : getr (ms_regs ms) 25 = w64 SHADOW_OFF)
  by (rewrite (cno_reg _ E _ ms 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact E25).
assert (R26 : getr (ms_regs ms) 26 = w64 (cno_F cx))
  by (rewrite (cno_reg _ E _ ms 26%bv 26 HS ltac:(vm_compute; reflexivity)); exact E26).
assert (R1 : getr (ms_regs ms) 1 = w64 0x81320)
  by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x81320 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (Hsite : cno_site B cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4)
  by exact (cno_site_of B cx E ssR W3 ms 2 ly3 S3 (c_U cx) md4 0x81320 HE U8 HS ltac:(vm_compute; reflexivity) HJ HARU
    Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
assert (Hg2 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
{ apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
  intros x Hx. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) x (KL x Hx)). }
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HbIn : In (b, cno_n cx + 18) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
assert (Hrq : 1 <= req_size (cno_n cx + 18) /\ cno_n cx + 18 <= req_size (cno_n cx + 18))
  by (apply req_size_pos; unfold cno_n; lia).
assert (KZ : forall p c, In (p, cno_n cx + 18) (ablocks B ly3 S3) ->
  zbytes_at tfibsegs W3 (ms_mem ms3) p (pn_copy (c_db cx) c) -> zbytes_at tfibsegs W3 (ms_mem ms) p (pn_copy (c_db cx) c)).
{ intros p c Hp Hzp. apply (cno_zbytes_kept W3 W3 (ms_mem ms3) (ms_mem ms) p _); [|exact Hzp].
  intros j Hj. rewrite (cno_pn_length (c_db cx) c) in Hj. fold (cno_n cx) in Hj.
  exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (p + j) (KB p (cno_n cx + 18) j Hp ltac:(lia))). }
pose proof (KZ a 65 HaIn Hza0) as Hza. pose proof (KZ b 66 HbIn Hzb0) as Hzb.
assert (Hk1 : 2 + 1 <= EV_check_no_overread) by (unfold EV_check_no_overread; lia).
assert (Hbb1 : blocks_bytes S3 + (cno_n cx + 18) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Hab, cno_bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  change (bsum [(a, cno_n cx + 18); (b, cno_n cx + 18)]) with (cno_n cx + 18 + (cno_n cx + 18 + 0)).
  unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES, cno_n in *. lia. }
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS eq_refl).
replace (ss_pc ssR) with PC_malloc by (vm_compute; reflexivity).
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_malloc) (ms_mem ms) (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs PC_malloc (ms_regs ms) (ms_mem ms) md4).
eapply SRr_bind.
{ exact (cno_call_mal cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)
    Hb Hsite R1 R10 Hg2 Hk1 Hbb1). }
cbv beta. intros W' c' _ (t & Hret).
pose (rF := match nth_error (ss_mem ssR) 1 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 120 (CVal 8 (SOff 46 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 1 rF 19 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  vm_compute. left. reflexivity. }
pose (rL := match nth_error (ss_mem ssR) 3 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 24 (CVal 8 (SOff 48 0)))).
{ apply (cno_chunk_at E ssR (w_H W3) ms 3 rL 9 _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  vm_compute. left. reflexivity. }
rewrite U19 in HcF. rewrite U9 in HcL.
destruct HE as (HE32 & HE33 & HE46 & HE47).
set (xs := fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t).
destruct (cno_resume B cx 2 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 1 (c_U cx) (fun _ => False) _ W' c' xs
  cno_flag_chunk cno_sl18 Hb Hsite Hret R9 R18 R19)
  as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
- intros x _ X. exact X.
- vm_compute. reflexivity.
- intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E ssR W3 ms (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS
    ltac:(vm_compute; reflexivity)))).
  intros j Hj. destruct (cno_E_env cx regs' a b t) as (_ & HX & _). exact (eq_trans (HX j Hj) (eq_sym (HE33 j Hj))).
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i _ X. exact X.
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcF). rewrite !fsw_SOff0.
  destruct (cno_E_env cx regs' a b t) as (_ & _ & X46 & _). exact (eq_trans X46 (eq_sym HE46)).
- intros regs' _. constructor; [|apply Forall_nil].
  apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E48.
  unfold xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbv beta in HPP. destruct HPP as (E10' & Ht0 & Hab' & Hg').
  assert (Era : raZ (ms_regs ms) = 0x81320) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  set (E' := Ereg regs' xs) in *.
  assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
    ew E' n = getr (ms_regs ms) r).
  { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
  assert (KZ' : forall p c, In (p, cno_n cx + 18) (ablocks B ly3 S3) ->
    zbytes_at tfibsegs W3 (ms_mem ms) p (pn_copy (c_db cx) c) -> zbytes_at tfibsegs W' mem' p (pn_copy (c_db cx) c)).
  { intros p c Hp Hzp. apply (cno_zbytes_kept W3 W' (ms_mem ms) mem' p _); [|exact Hzp].
    intros j Hj. rewrite (cno_pn_length (c_db cx) c) in Hj. fold (cno_n cx) in Hj.
    apply (HBK p (cno_n cx + 18) j Hp); [rewrite Hab'; apply in_or_app; left; exact Hp | lia | intros X; exact X]. }
  apply (HNX cx E' (2 + 1) ly' S' (c_U cx) W' (mkst regs' (Z_to_bv 64 0x81320) mem' (seg_rom tfibsegs)) md' Hb
    (cno_E_env cx regs' a b t) HJ' HARU').
  + exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [ms_mem mkst]; rewrite Hab', Hab, <- app_assoc; reflexivity|].
    split; [exact Ha0|]. split; [exact Ha16|]. split; [exact Hb0|]. split; [exact Hb16|]. split; [exact Ht0|].
    split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
      (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
      (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
      (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
    split; [subst E'; unfold xs; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; unfold xs; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; unfold xs; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity|].
    split; [subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact E10'|].
    split; [rewrite (KR 20%bv 20%nat eq_refl ltac:(cno_cs)); exact R20|].
    split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
    split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
    split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
    split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
    split; [rewrite (KR 26%bv 26%nat eq_refl ltac:(cno_cs)); exact R26|].
    split; [exact (KZ' a 65 HaIn Hza)|]. split; [exact (KZ' b 66 HbIn Hzb)|].
    split; [exact Hg' | exact Hh'].
  + exact HS'.
Qed.

(* the boundary record read off a symbolic state with the walk's four regions *)
Lemma cno_mframe_of_st : forall cx E ss (W : world tfibsegs) ms md k ly S U A e16,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  cno_J B cx k ly S W (unpoison U (ms_mem ms)) md -> ARU tfibsegs B ly S U W (ms_mem ms) md ->
  FSupoisonU.fs_heads B ly S U ->
  getr (ms_regs ms) 2 = w64 (cno_sp1 cx) -> getr (ms_regs ms) 8 = w64 (cno_sp0 cx) ->
  getr (ms_regs ms) 9 = w64 (cno_sp1 cx) -> getr (ms_regs ms) 18 = w64 (cno_SF cx) ->
  getr (ms_regs ms) 19 = w64 (cno_F cx) -> getr (ms_regs ms) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms) 4 = getr (c_regs cx) 4 ->
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  (forall j, (j < 13)%nat -> ew E (33 + j) = getr (c_regs cx) (nth j cno_saved_regs 0%bv)) ->
  ew E 46 = w64 (cno_FL cx) -> sv_denot E e16 = w64 (cno_F cx) -> 0 <= cno_F cx < 2 ^ 64 ->
  ew E 48 = w64 A -> 0 <= A < 2 ^ 64 ->
  nth_error (ss_mem ss) 0 = Some (fs_ret_s0_region (-104) 0 cno_sv_chunks) ->
  (forall r1, nth_error (ss_mem ss) 1 = Some r1 -> YP09.r_base r1 = Some 19%nat /\
     In (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) (YP09.r_chunks r1)) ->
  (forall r3, nth_error (ss_mem ss) 3 = Some r3 -> YP09.r_base r3 = Some 9%nat /\
     In (YP09.mkChunk 16 (CVal 8 e16)) (YP09.r_chunks r3) /\ In (YP09.mkChunk 24 (CVal 8 (SOff 48 0))) (YP09.r_chunks r3)) ->
  (exists r1, nth_error (ss_mem ss) 1 = Some r1) -> (exists r3, nth_error (ss_mem ss) 3 = Some r3) ->
  cno_mframe B cx k ly S U W (ms_regs ms) (ms_mem ms) md A.
Proof.
intros cx E ss W ms md k ly S U A e16 HS HJ HARU Hh R2 R8 R9 R18 R19 R3 R4 U8 U19 U9 ES E46 E16 HF64 E48 HA
  H0 H1 H3 (r1 & Hr1) (r3 & Hr3).
destruct (H1 r1 Hr1) as (Hb1 & Hc1). destruct (H3 r3 Hr3) as (Hb3 & Hc16 & Hc24).
split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
do 7 (split; [assumption|]).
split; [|split; [|split]].
- intros j Hj.
  assert (Hc : In (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0))) (YP09.r_chunks
    (fs_ret_s0_region (-104) 0 cno_sv_chunks))).
  { cbn [fs_ret_s0_region YP09.r_chunks]. unfold cno_sv_chunks.
    apply (in_map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0)))). apply in_seq. lia. }
  pose proof (cno_val_at E ss (w_H W) ms 0 _ 8 _ 8%N (SOff (33 + j) 0)
    (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv))) HS H0 eq_refl Hc) as X.
  rewrite U8 in X. replace (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx - 8 * (Z.of_nat j + 1)) in X by lia.
  apply X; [|apply u64_range|cbn; lia].
  rewrite fsw_SOff0, Z_to_bv_bv_unsigned. exact (ES j Hj).
- pose proof (cno_val_at E ss (w_H W) ms 1 r1 19 120 8%N (SOff 46 0) (bv_unsigned (w64 (cno_FL cx))) HS Hr1 Hb1 Hc1) as X.
  rewrite U19 in X. apply X; [|apply u64_range|cbn; lia].
  rewrite fsw_SOff0, Z_to_bv_bv_unsigned. exact E46.
- pose proof (cno_val_at E ss (w_H W) ms 3 r3 9 16 8%N e16 (cno_F cx) HS Hr3 Hb3 Hc16) as X.
  rewrite U9 in X. apply X; [exact E16 | exact HF64 | cbn; lia].
- pose proof (cno_val_at E ss (w_H W) ms 3 r3 9 24 8%N (SOff 48 0) A HS Hr3 Hb3 Hc24) as X.
  rewrite U9 in X. apply X; [rewrite fsw_SOff0; exact E48 | exact HA | cbn; lia].
Qed.

(* ---- MS: the machine at the __asan_memset call (0x81354, ra 0x81358): memset (t + len, 0, 17); s6 = t + len + 17,
   s9 = SHADOW_OFF; t holds d's bytes (0x81338; nothing when len = 0) ---- *)
Definition INV_MS : cno_minv := fun cx k ly S U W regs mem md => exists a b t,
  U = c_U cx /\ k = 3 /\ cno_mframe B cx k ly S U W regs mem md a /\
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\
  getr regs 1 = w64 0x81358 /\ getr regs 10 = w64 (t + cno_n cx) /\ getr regs 11 = w64 0 /\
  getr regs 12 = w64 17 /\ getr regs 20 = w64 b /\ getr regs 21 = w64 t /\
  getr regs 22 = w64 (t + cno_n cx + 17) /\ getr regs 25 = w64 SHADOW_OFF /\
  zbytes_at tfibsegs W mem a (pn_copy (c_db cx) 65) /\ zbytes_at tfibsegs W mem b (pn_copy (c_db cx) 66) /\
  zbytes_at tfibsegs W mem t (c_db cx) /\
  fs_glob tfibsegs W mem (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx).

(* the write window of the inline check's run: cno_awr's four regions, the byte x of a block the walk made, the
   read-only shadow byte *)
Lemma cno_awr_S : forall E STK sp0 FP bl0 blc ly fr0 pos F sp1 x,
  bv_unsigned (ew E 8) = sp0 -> bv_unsigned (ew E 19) = F -> bv_unsigned (ew E 18) = shadow_addr F ->
  bv_unsigned (ew E 9) = sp1 -> F = frame_addr ly 1 pos -> 104 <= STK -> sp0 - STK <= sp1 + 16 -> sp1 + 56 <= sp0 ->
  bv_unsigned (ew E 22) = x -> in_tmp_block bl0 blc x ->
  awr_ok tfibsegs B E (ss_mem ss_S) STK sp0 FP bl0 blc ly [(1, pos)] fr0.
Proof.
intros E STK sp0 FP bl0 blc ly fr0 pos F sp1 x E8 EF ES E9 HF HSTK Hw1 Hw2 E22 Htmp.
lazymatch goal with |- awr_ok ?sg ?bs ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?l ?own ?f0 =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bs E0 rs' stk s0 fp b0 bc l own f0) end.
eapply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_gen with (k := 19%nat) (b := F); [reflexivity | exact EF | |].
{ intros a Ha. left. right; right; right. exists 1, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd YP09.r_wlo YP09.r_whi] in *. change (fs_frame_bytes 1) with 128. rewrite <- HF. lia. }
eapply awr_ok_cons_gen with (k := 18%nat) (b := shadow_addr F); [reflexivity | exact ES | |].
{ intros a Ha. left. right; right; right. exists 1, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd YP09.r_wlo YP09.r_whi] in *. change (fs_frame_bytes 1 / 8) with 16. rewrite <- HF. lia. }
eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0); [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia |].
eapply awr_ok_cons_gen with (k := 22%nat) (b := x); [reflexivity | exact E22 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with x by lia. left. right; right; left. exact Htmp. }
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
Qed.

Ltac cno_awrS E U8 U19 U18 U9 EFa U22 Htmp FS N4 :=
  intros a0 Ha0; eapply (cno_awr_S E);
  [exact U8 | exact U19 | exact U18 | exact U9 | exact (eq_sym EFa) | clear - FS; lia | clear - FS N4; lia
  | clear - N4; lia | exact U22 | exact Htmp
  | eapply (cno_wr_skel E _ _ a0); [ | exact Ha0]; vm_compute; reflexivity].
(* ---- from the memset call: the call, the inline check 0x81358-0x81364 (slow path 0x81550-0x81554; never
   0x81558 / 0x8155c), the stores 0x81368-0x8138c, the run to the first decode call ---- *)
Lemma cno_seg_MS : cno_at B A_preset_base64_decode (INV_D1 B) -> cno_at B PC_memset INV_MS.
Proof.
intros HD cx k ly S U W regs mem md Hb
  (a & b & t & -> & -> & Hm & Hab & R1 & R10 & R11 & R12 & R20 & R21 & R22 & R25 & Hza & Hzb & Hzt & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _).
assert (Hn0 : 0 <= cno_n cx <= PRESET_FILE_MAX_BYTES) by (unfold cno_n in *; lia).
pose proof Hm as (HJ & HARU & Hh & M2 & M8 & M9 & M18 & M19 & M3 & M4 & Msv & MFL & MS16 & MS24).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly S (c_U cx) W mem md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
(* the raw blocks *)
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HtIn : In (t, cno_n cx + 18) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; right; right; left; reflexivity).
destruct (fsw_ablock_low B ly S W (unpoison (c_U cx) mem) md t _ HAR HtIn) as (Lt1 & Lt2 & Lt3).
destruct (fsw_ablock_low B ly S W (unpoison (c_U cx) mem) md a _ HAR HaIn) as (La1 & La2 & La3).
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md t _ 1 (c_fpos cx) HAR HtIn Hin) as Htf.
rewrite EFa in Htf. change (fs_frame_bytes 1) with 128 in Htf. unfold zdisjoint in Htf. cbn [fst snd] in Htf.
pose proof (fsw_ablock_off_shadow B ly S W (unpoison (c_U cx) mem) md t _ HAR HtIn) as Hts.
(* the call *)
assert (Hsite : cno_site B cx 3 ly S (c_U cx) W regs mem md)
  by exact (cno_site_of_mframe B cx 3 ly S (c_U cx) W regs mem md a 0x81358 Hm R1 ltac:(lia) ltac:(reflexivity)).
eapply SRr_bind.
{ exact (cno_call_mset cx 3 ly S (c_U cx) W regs mem md t Hb Hsite eq_refl R1 R10 R11 R12
    (ex_intro _ [(a, cno_n cx + 18); (b, cno_n cx + 18)] Hab)). }
cbv beta. intros W' c' _ Hret.
destruct (cno_mframe_resume B cx 3 ly S (c_U cx) W regs mem md a b t [] 0 (c_U cx) _ _ W' c' Hb Hm Hsite
  ltac:(lia) Hret) as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS0).
{ intros x Hx Hk. cbv beta in Hk. lia. }
{ intros i Hi Hk. cbv beta in Hk. lia. }
{ intros i Hi Hk. cbv beta in Hk. lia. }
destruct HPP as (-> & -> & -> & Ea0 & Hz17 & Hout & Hra).
assert (Era : raZ regs = 0x81358) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
rewrite Era in Ec, HS0. subst c'.
set (x := t + cno_n cx + 17) in *.
destruct (Hra x ltac:(unfold x; lia)) as (s & Hsv & Hsok).
assert (Hs07 : 0 <= s <= 7) by (destruct Hsok as [-> | Hsok]; lia).
set (ms1 := mkst regs' (Z_to_bv 64 0x81358) mem' (seg_rom tfibsegs)) in *.
set (extra := [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]).
pose proof (cno_st_lift cx a b t extra W regs' ss_S0 ms1 HS0 ltac:(vm_compute; reflexivity)) as HS1.
set (E := Ereg regs' (cno_xs cx a b t extra)) in *.
assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) -> ew E n = getr regs r).
{ intros r n Hn' Hc. subst E. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite (KR 8%bv 8%nat eq_refl ltac:(cno_cs)), M8; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), M9; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), M19; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite (KR 18%bv 18%nat eq_refl ltac:(cno_cs)), M18; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
assert (R22' : getr regs' 22 = w64 x) by (rewrite (fsw_pres _ _ 22%bv HP ltac:(cno_cs)); exact R22).
assert (R25' : getr regs' 25 = w64 SHADOW_OFF) by (rewrite (fsw_pres _ _ 25%bv HP ltac:(cno_cs)); exact R25).
assert (U22 : bv_unsigned (ew E 22) = x) by (subst E; rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl), R22'; apply wz; lia).
assert (U52 : bv_unsigned (ew E 52) = SHADOW_OFF + x / 8)
  by (subst E; change 52%nat with (32 + 20)%nat; rewrite ew_Ereg_extra; cbn; apply wz; unfold SHADOW_OFF in *;
      Z.div_mod_to_equations; lia).
(* F is 32-aligned (the atom fact of the frame) *)
assert (HFal : cno_F cx mod 32 = 0).
{ pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & (HA0 & _ & _)).
  cbn [ss_facts cno_ss fss_ret_s0_args f_atoms cno_gf atoms_ok] in HA0.
  destruct HA0 as (_ & (_ & HA19 & _) & _). cbn [af_al2] in HA19. change (2 ^ 5) with 32 in HA19. rewrite <- U19.
  replace (bv_unsigned (ew E 19)) with (bv_unsigned (ew (Ereg regs' (cno_xs cx a b t [])) 19)); [exact HA19|].
  subst E. rewrite !(ew_Ereg_nat regs' _ 19 19%bv eq_refl). reflexivity. }
pose proof (ARU_AR tfibsegs B ly S (c_U cx) W mem' md' HARU') as HAR'.
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison (c_U cx) mem') md' t _ HAR' HtIn)
  as (_ & _ & _ & _ & Hpres & Hpw & _).
assert (Hw : writable_at tfibsegs (mrestrict (w_H W) mem') x).
{ destruct (proj1 (Hpres x ltac:(unfold x; lia))) as (Hh0 & bb & Hbb).
  rewrite (fsw_unpoison_app B ly S (c_U cx) W mem' md' x HARU' ltac:(unfold x; lia) (Hts x ltac:(unfold x; lia))) in Hbb.
  exact (cno_apw _ _ _ (conj Hh0 (ex_intro _ bb Hbb))). }
assert (HS2 : st_ok tfibsegs E ss_S (restrict (w_H W) ms1)).
{ apply (cno_ssS_ok cx a b t x s W ms1 HS1 R22' R25' ltac:(unfold x; lia) Hs07 Hw Hsv).
  - change (Ereg (ms_regs ms1) (cno_xs cx a b t [w64 (x / 8); w64 (SHADOW_OFF + x / 8); w64 s; w64 (x mod 8)]))
      with E.
    lazymatch goal with |- forall r, In r ?L -> _ => let L' := eval vm_compute in L in change L with L' end.
    pose proof (Hts x ltac:(unfold x; lia)) as Hxs.
    intros r [<- | [<- | [<- | [<- | []]]]]; unfold extent_disjoint, cno_R22, cno_R52;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fs_ret_s0_region fstk_ret];
      rewrite ?U8, ?U9, ?U19, ?U18, U22, U52; unfold cno_SF, shadow_addr, x in *; unfold in_app, kLowShadowBeg, ASAN_CEIL,
      SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; split; Z.div_mod_to_equations; lia.
  - pose proof (Hts x ltac:(unfold x; lia)) as Hxs. unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
assert (Htmp : in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) x).
{ exists t, (cno_n cx + 18). split; [exact HtIn|]. split; [|unfold x; lia].
  rewrite Hab in Hpw. apply (cno_fresh _ (cno_raw cx a b t) _ Hpw); [right; right; left; reflexivity | cbn [snd]; lia]. }
assert (FIN : forall msF mdF,
  st_ok tfibsegs E cno_ssD (restrict (w_H W) msF) ->
  cno_J B cx (3 + 0) ly S W (unpoison (c_U cx) (ms_mem msF)) mdF ->
  ARU tfibsegs B ly S (c_U cx) W (ms_mem msF) mdF ->
  (forall y : word, ~ in_wrange E (ss_mem ss_S) (bv_unsigned y) -> ms_mem msF y = mem' y) ->
  SRr tfibsegs W (mkCfg msF mdF) (cno_post B cx)).
{ intros msF mdF HSF HJF HARUF HKF.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E cno_ssD msF HSF eq_refl).
  replace (ss_pc cno_ssD) with A_preset_base64_decode by (vm_compute; reflexivity).
  change (mkCfg (mkst (ms_regs msF) (Z_to_bv 64 A_preset_base64_decode) (ms_mem msF) (seg_rom tfibsegs)) mdF)
    with (cfg_at tfibsegs A_preset_base64_decode (ms_regs msF) (ms_mem msF) mdF).
  apply (HD cx 3 ly S (c_U cx) W (ms_regs msF) (ms_mem msF) mdF Hb).
  (* registers *)
  assert (G : forall (r : bv 5) n, sr_get (ss_regs cno_ssD) r = SOff n 0 -> getr (ms_regs msF) r = ew E n)
    by (intros r n Hr; exact (cno_reg (w_H W) E cno_ssD msF r n HSF Hr)).
  assert (EF19 : ew E 19 = w64 (cno_F cx)) by (rewrite (KR 19%bv 19%nat eq_refl ltac:(cno_cs)); exact M19).
  assert (E48 : ew E 48 = w64 a) by (subst E; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F2 : getr (ms_regs msF) 2 = w64 (cno_sp1 cx))
    by (rewrite (G 2%bv 2%nat ltac:(vm_compute; reflexivity)), (KR 2%bv 2%nat eq_refl ltac:(cno_cs)); exact M2).
  assert (F8 : getr (ms_regs msF) 8 = w64 (cno_sp0 cx))
    by (rewrite (G 8%bv 8%nat ltac:(vm_compute; reflexivity)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)); exact M8).
  assert (F9 : getr (ms_regs msF) 9 = w64 (cno_sp1 cx))
    by (rewrite (G 9%bv 9%nat ltac:(vm_compute; reflexivity)), (KR 9%bv 9%nat eq_refl ltac:(cno_cs)); exact M9).
  assert (F18 : getr (ms_regs msF) 18 = w64 (cno_SF cx))
    by (rewrite (G 18%bv 18%nat ltac:(vm_compute; reflexivity)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)); exact M18).
  assert (F19 : getr (ms_regs msF) 19 = w64 (cno_F cx))
    by (rewrite (G 19%bv 19%nat ltac:(vm_compute; reflexivity)); exact EF19).
  assert (F3 : getr (ms_regs msF) 3 = getr (c_regs cx) 3)
    by (rewrite (G 3%bv 3%nat ltac:(vm_compute; reflexivity)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)); exact M3).
  assert (F4 : getr (ms_regs msF) 4 = getr (c_regs cx) 4)
    by (rewrite (G 4%bv 4%nat ltac:(vm_compute; reflexivity)), (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); exact M4).
  assert (F20 : getr (ms_regs msF) 20 = w64 b)
    by (rewrite (G 20%bv 20%nat ltac:(vm_compute; reflexivity)), (KR 20%bv 20%nat eq_refl ltac:(cno_cs)); exact R20).
  assert (F21 : getr (ms_regs msF) 21 = w64 t)
    by (rewrite (G 21%bv 21%nat ltac:(vm_compute; reflexivity)), (KR 21%bv 21%nat eq_refl ltac:(cno_cs)); exact R21).
  assert (F10 : getr (ms_regs msF) 10 = w64 a) by (rewrite (G 10%bv 48%nat ltac:(vm_compute; reflexivity)); exact E48).
  assert (FO : forall (r : bv 5) z, sr_get (ss_regs cno_ssD) r = SOff 19 z -> 0 <= z <= 96 ->
    getr (ms_regs msF) r = w64 (cno_F cx + z))
    by (intros r z Hr Hz; exact (cno_reg_off (w_H W) E cno_ssD msF r 19 z (cno_F cx) HSF Hr EF19 HF64 ltac:(lia))).
  assert (F1 : getr (ms_regs msF) 1 = w64 0x8139c)
    by exact (fsw_reg_lit (w_H W) E cno_ssD msF 1%bv 0x8139c HSF ltac:(vm_compute; reflexivity) ltac:(lia)).
  (* the windows of the check's run: the zone and x *)
  assert (WZ : forall y, in_wrange E (ss_mem ss_S) y -> cno_zone cx y \/ y = x).
  { intros y (rg & Hrg & Hw0).
    lazymatch type of Hrg with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrg end.
    destruct Hrg as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw0; rewrite ?U8, ?U9, ?U19, ?U18, ?U22, ?U52 in Hw0;
      unfold cno_zone; lia. }
  assert (KF : forall y, 0 <= y < 2 ^ 64 -> ~ cno_zone cx y -> y <> x ->
    aview tfibsegs (w_H W) (ms_mem msF) y = aview tfibsegs (w_H W) mem' y).
  { intros y Hy Hz Hx'. apply aview_at. apply HKF. rewrite (wz y Hy). intros Hw0. destruct (WZ y Hw0); auto. }
  (* the blocks a / b against t *)
  pose proof Hpw as Hpw0. rewrite Hab, map_app in Hpw0. apply pairwise_app_l in Hpw0 as (_ & Hpw0).
  cbn [cno_raw map pairwise fst snd] in Hpw0.
  destruct Hpw0 as (HFa & HFb & _). apply Forall_cons_iff in HFa as (Dab & HFa). apply Forall_cons_iff in HFa as (Dat & _).
  apply Forall_cons_iff in HFb as (Dbt & _). unfold zdisjoint in Dab, Dat, Dbt. cbn [fst snd] in Dab, Dat, Dbt.
  assert (HbIn : In (b, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W (unpoison (c_U cx) mem) md b _ HAR HbIn) as (Lb1 & Lb2 & Lb3).
  assert (KB : forall p, In (p, cno_n cx + 18) (ablocks B ly S) -> (p + req_size (cno_n cx + 18) <= t \/ t + req_size (cno_n cx + 18) <= p) ->
    forall j, 0 <= j < req_size (cno_n cx + 18) ->
    aview tfibsegs (w_H W) (ms_mem msF) (p + j) = aview tfibsegs (w_H W) mem (p + j)).
  { intros p Hp Hpt j Hj.
    destruct (fsw_ablock_low B ly S W (unpoison (c_U cx) mem) md p _ HAR Hp) as (Lp1 & Lp2 & Lp3).
    rewrite (KF (p + j) ltac:(lia) (cno_zone_blk B cx ly S (c_U cx) W mem' md' p _ j Hb HARU' Hin EF Hp Hj)
      ltac:(unfold x; lia)).
    exact (HBK p _ j Hp Hp Hj ltac:(cbv beta; lia)). }
  exists a, b, t.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { (* cno_mframe *)
    split; [exact HJF|]. split; [exact HARUF|]. split; [exact Hh'|].
    split; [exact F2|]. split; [exact F8|]. split; [exact F9|]. split; [exact F18|]. split; [exact F19|].
    split; [exact F3|]. split; [exact F4|].
    split; [|split; [|split]].
    - intros j Hj.
      assert (Hc : In (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0))) (YP09.r_chunks (cno_rD 0))).
      { replace (YP09.r_chunks (cno_rD 0)) with cno_sv_chunks by (vm_compute; reflexivity).
        unfold cno_sv_chunks. apply (in_map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0)))).
        apply in_seq. lia. }
      pose proof (cno_val_at E cno_ssD (w_H W) msF 0 (cno_rD 0) 8 _ 8%N (SOff (33 + j) 0)
        (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv))) HSF ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) Hc) as X.
      rewrite U8 in X. replace (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx - 8 * (Z.of_nat j + 1)) in X by lia.
      apply X; [|apply u64_range|cbn; lia].
      rewrite fsw_SOff0, Z_to_bv_bv_unsigned. subst E. change (33 + j)%nat with (32 + Datatypes.S j)%nat.
      rewrite ew_Ereg_extra. unfold cno_xs. do 13 (destruct j as [|j]; [reflexivity|]). lia.
    - pose proof (cno_val_at E cno_ssD (w_H W) msF 1 (cno_rD 1) 19 120 8%N (SOff 46 0) (bv_unsigned (w64 (cno_FL cx)))
        HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cno_inc)) as X.
      rewrite U19 in X. apply X; [|apply u64_range|cbn; lia].
      rewrite fsw_SOff0, Z_to_bv_bv_unsigned. subst E. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity.
    - pose proof (cno_val_at E cno_ssD (w_H W) msF 3 (cno_rD 3) 9 16 8%N (SOff 19 0) (cno_F cx)
        HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cno_inc)) as X.
      rewrite U9 in X. apply X; [rewrite fsw_SOff0; exact EF19 | exact HF64 | cbn; lia].
    - pose proof (cno_val_at E cno_ssD (w_H W) msF 3 (cno_rD 3) 9 24 8%N (SOff 48 0) a
        HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cno_inc)) as X.
      rewrite U9 in X. apply X; [rewrite fsw_SOff0; exact E48 | lia | cbn; lia]. }
  split; [exact Hab|].
  split; [exact F1|]. split; [exact F10|].
  split; [exact (FO 11%bv 32 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact F20|]. split; [exact F21|].
  split; [exact (FO 23%bv 64 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (FO 26%bv 32 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (FO 27%bv 96 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split.
  { apply (cno_zbytes_kept W W mem (ms_mem msF) a _); [|exact Hza].
    intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj. fold (cno_n cx) in Hj.
    apply (KB a HaIn ltac:(lia) j ltac:(lia)). }
  split.
  { apply (cno_zbytes_kept W W mem (ms_mem msF) b _); [|exact Hzb].
    intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj. fold (cno_n cx) in Hj.
    apply (KB b HbIn ltac:(lia) j ltac:(lia)). }
  pose proof (fsw_ablock_off_img B ly S W (unpoison (c_U cx) mem) md t _ HAR HtIn) as Ltimg.
  split.
  { intros j Hj. rewrite length_app, repeat_length in Hj.
    assert (Hn' : cno_n cx = Z.of_nat (length (c_db cx))) by reflexivity.
    assert (Hj' : 0 <= Z.of_nat j < cno_n cx + 18) by lia.
    destruct (Z_lt_le_dec (Z.of_nat j) (cno_n cx)) as [Hlt | Hge].
    - rewrite app_nth1 by lia.
      destruct (Hzt j ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
      apply (cno_vm1_kept (w_H W) (w_H W) mem (ms_mem msF)); [|exact Hv].
      rewrite (KF (t + Z.of_nat j) ltac:(lia)
        (cno_zone_blk B cx ly S (c_U cx) W mem' md' t _ (Z.of_nat j) Hb HARU' Hin EF HtIn ltac:(lia)) ltac:(unfold x; lia)).
      exact (HBK t _ (Z.of_nat j) HtIn HtIn ltac:(lia) ltac:(cbv beta; lia)).
    - rewrite app_nth2 by lia. rewrite nth_repeat. split; [|lia].
      destruct (Z.eq_dec (Z.of_nat j) (cno_n cx + 17)) as [Heq | Hne].
      + pose proof (cno_val_at E cno_ssD (w_H W) msF 4 (cno_rD 4) 22 0 1%N (SLit 0) 0
          HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cno_inc)) as X.
        rewrite U22, Z.add_0_r in X. replace (t + Z.of_nat j) with x by (unfold x; lia).
        apply X; [reflexivity | lia | cbn; lia].
      + destruct (Hz17 (j - length (c_db cx))%nat ltac:(rewrite repeat_length; lia)) as (Hv & _).
        rewrite nth_repeat in Hv.
        replace (t + cno_n cx + Z.of_nat (j - length (c_db cx))) with (t + Z.of_nat j) in Hv by lia.
        apply (cno_vm1_kept (w_H W) (w_H W) mem' (ms_mem msF)); [|exact Hv].
        apply KF; [lia | | unfold x; lia].
        exact (cno_zone_blk B cx ly S (c_U cx) W mem' md' t _ (Z.of_nat j) Hb HARU' Hin EF HtIn ltac:(lia)). }
  assert (LOC : forall z, z = 32 \/ z = 64 \/ z = 96 ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem msF)) (cno_F cx + z) 8 0).
  { intros z Hz.
    assert (Hc : In (YP09.mkChunk z (CVal 8 (SLit 0))) (YP09.r_chunks (cno_rD 1)))
      by (destruct Hz as [-> | [-> | ->]]; cno_inc).
    pose proof (cno_val_at E cno_ssD (w_H W) msF 1 (cno_rD 1) 19 z 8%N (SLit 0) 0
      HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hc) as X.
    rewrite U19 in X. apply X; [reflexivity | lia | cbn; lia]. }
  assert (RA : forall z, z = 32 \/ z = 64 \/ z = 96 ->
    range_addressable (aview tfibsegs (w_H W) (ms_mem msF)) SHADOW_OFF (cno_F cx + z) 8).
  { intros z Hz.
    assert (Hc : In (YP09.mkChunk (z / 8) (CVal 1 (SLit 0))) (YP09.r_chunks (cno_rD 2)))
      by (destruct Hz as [-> | [-> | ->]]; cno_inc).
    pose proof (cno_val_at E cno_ssD (w_H W) msF 2 (cno_rD 2) 18 (z / 8) 1%N (SLit 0) 0
      HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hc) as X.
    rewrite U18 in X. specialize (X eq_refl ltac:(lia) ltac:(cbn; lia)).
    pose proof (ACem.aview_of_val_mem1 tfibsegs (w_H W) (ms_mem msF) _ 0 X ltac:(lia)) as Hav.
    intros y Hy. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF y) with (cno_SF cx + z / 8); [exact Hav|].
    unfold shadow_of_addr, cno_SF, shadow_addr. destruct Hz as [-> | [-> | ->]]; Z.div_mod_to_equations; lia. }
  split; [exact (LOC 32 ltac:(lia))|]. split; [exact (LOC 64 ltac:(lia))|]. split; [exact (LOC 96 ltac:(lia))|].
  split; [exact (RA 32 ltac:(lia))|]. split; [exact (RA 64 ltac:(lia))|]. split; [exact (RA 96 ltac:(lia))|].
  apply (cno_glob_ledger W W mem (ms_mem msF) _ _ _ _); [|exact Hg].
  intros y Hy. pose proof (cno_pstat_bounds y Hy) as Hyb.
  rewrite (KF y ltac:(lia) (cno_zone_ledger B cx ly S (c_U cx) W mem' md' y Hb HARU' Hin EF Hy)
    ltac:(unfold x, FS_IMG_END in *; lia)).
  apply Hout; [lia | unfold FS_IMG_END in *; lia | unfold ESTACK; lia]. }
assert (HE53 : ew E 53 = w64 s) by (subst E; change 53%nat with (32 + 21)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HE54 : ew E 54 = w64 (x mod 8)) by (subst E; change 54%nat with (32 + 22)%nat; rewrite ew_Ereg_extra; reflexivity).
(* to the check's branch 0x81364 *)
fsw_aj_runU cno_tbl_ok HS2 HJ' HARU'.
{ cno_awrS E U8 U19 U18 U9 EFa U22 Htmp FS N4. }
rename ms into ms2.
lazymatch type of HS2 with st_ok _ _ ?ss _ =>
  eapply (SRr_sym_branch tfibsegs W E ss ms2 _ (cno_post B cx) BC_NE (SOff 53 0) (SLit 0) HS2) end;
  intros Hbr HSb.
- (* a non-zero shadow byte: the slow path 0x81550 / 0x81554 *)
  fsw_aj_runU cno_tbl_ok HSb HJ' HARU'.
  { cno_awrS E U8 U19 U18 U9 EFa U22 Htmp FS N4. }
  rename ms into ms3.
  lazymatch type of HSb with st_ok _ _ ?ss _ =>
    eapply (SRr_sym_branch tfibsegs W E ss ms3 _ (cno_post B cx) BC_LT (SOff 54 0) (SOff 53 0) HSb) end;
    intros Hbr2 HSc.
  + fsw_aj_run_toU cno_tbl_ok HSc HJ' HARU' A_preset_base64_decode.
    { cno_awrS E U8 U19 U18 U9 EFa U22 Htmp FS N4. }
    cno_dropc HSc HSd.
    apply (FIN ms _ HSd HJ' HARU').
    intros y Hy.
    assert (Sk : forall rs, map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
      map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem ss_S) -> ~ in_wrange E rs (bv_unsigned y))
      by (intros rs Hrs Hw0; exact (Hy (cno_wr_skel E rs (ss_mem ss_S) _ Hrs Hw0))).
    rewrite (HF1 y), (HF0 y), (HF y Hy); [reflexivity | apply Sk; vm_compute; reflexivity | apply Sk; vm_compute; reflexivity].
  + exfalso. cbn [branch_taken] in Hbr, Hbr2.
    rewrite fsw_SOff0, HE53 in Hbr. rewrite !fsw_SOff0, HE53, HE54 in Hbr2.
    destruct Hsok as [Hs0 | (Hlt & Hs8)].
    * subst s. vm_compute in Hbr. discriminate Hbr.
    * rewrite bv_lts_signed in Hbr2. unfold w64 in Hbr2.
      rewrite !signed_of_small in Hbr2 by (rewrite wz by (Z.div_mod_to_equations; lia); unfold half64; Z.div_mod_to_equations; lia).
      rewrite !wz in Hbr2 by (Z.div_mod_to_equations; lia). apply Z.ltb_ge in Hbr2. lia.
- (* a zero shadow byte *)
  fsw_aj_run_toU cno_tbl_ok HSb HJ' HARU' A_preset_base64_decode.
  { cno_awrS E U8 U19 U18 U9 EFa U22 Htmp FS N4. }
  cno_dropc HSb HSd.
  apply (FIN ms _ HSd HJ' HARU').
  intros y Hy.
  assert (Sk : forall rs, map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs =
    map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) (ss_mem ss_S) -> ~ in_wrange E rs (bv_unsigned y))
    by (intros rs Hrs Hw0; exact (Hy (cno_wr_skel E rs (ss_mem ss_S) _ Hrs Hw0))).
  rewrite (HF0 y), (HF y Hy); [reflexivity | apply Sk; vm_compute; reflexivity].
Qed.

(* the memset call site read off a symbolic state: INV_MS, and on to the first decode call *)
Lemma cno_MS_of : forall cx E ss (W : world tfibsegs) ms md ly S a b t e16,
  cno_at B PC_memset INV_MS -> cno_base B cx -> cno_E cx E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ss_pc ss = PC_memset -> ss_resv ss = None ->
  cno_J B cx 3 ly S W (unpoison (c_U cx) (ms_mem ms)) md -> ARU tfibsegs B ly S (c_U cx) W (ms_mem ms) md ->
  FSupoisonU.fs_heads B ly S (c_U cx) ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ->
  getr (ms_regs ms) 2 = w64 (cno_sp1 cx) -> getr (ms_regs ms) 8 = w64 (cno_sp0 cx) ->
  getr (ms_regs ms) 9 = w64 (cno_sp1 cx) -> getr (ms_regs ms) 18 = w64 (cno_SF cx) ->
  getr (ms_regs ms) 19 = w64 (cno_F cx) -> getr (ms_regs ms) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms) 4 = getr (c_regs cx) 4 ->
  getr (ms_regs ms) 1 = w64 0x81358 -> getr (ms_regs ms) 10 = w64 (t + cno_n cx) -> getr (ms_regs ms) 11 = w64 0 ->
  getr (ms_regs ms) 12 = w64 17 -> getr (ms_regs ms) 20 = w64 b -> getr (ms_regs ms) 21 = w64 t ->
  getr (ms_regs ms) 22 = w64 (t + cno_n cx + 17) -> getr (ms_regs ms) 25 = w64 SHADOW_OFF ->
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  sv_denot E e16 = w64 (cno_F cx) -> 0 <= cno_F cx < 2 ^ 64 -> ew E 48 = w64 a -> 0 <= a < 2 ^ 64 ->
  nth_error (ss_mem ss) 0 = Some (fs_ret_s0_region (-104) 0 cno_sv_chunks) ->
  (forall r1, nth_error (ss_mem ss) 1 = Some r1 -> YP09.r_base r1 = Some 19%nat /\
     In (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) (YP09.r_chunks r1)) ->
  (forall r3, nth_error (ss_mem ss) 3 = Some r3 -> YP09.r_base r3 = Some 9%nat /\
     In (YP09.mkChunk 16 (CVal 8 e16)) (YP09.r_chunks r3) /\ In (YP09.mkChunk 24 (CVal 8 (SOff 48 0))) (YP09.r_chunks r3)) ->
  (exists r1, nth_error (ss_mem ss) 1 = Some r1) -> (exists r3, nth_error (ss_mem ss) 3 = Some r3) ->
  zbytes_at tfibsegs W (ms_mem ms) a (pn_copy (c_db cx) 65) -> zbytes_at tfibsegs W (ms_mem ms) b (pn_copy (c_db cx) 66) ->
  zbytes_at tfibsegs W (ms_mem ms) t (c_db cx) ->
  fs_glob tfibsegs W (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) ->
  SRr tfibsegs W (mkCfg ms md) (cno_post B cx).
Proof.
intros cx E ss W ms md ly S a b t e16 HMS Hb HE HS Hpc Hrv HJ HARU Hh Hab R2 R8 R9 R18 R19 R3 R4 R1 R10 R11 R12 R20 R21
  R22 R25 U8 U19 U9 E16 HF64 E48 HA H0 H1 H3 Hr1 Hr3 Hza Hzb Hzt Hg.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv), Hpc.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_memset) (ms_mem ms) (seg_rom tfibsegs)) md)
  with (cfg_at tfibsegs PC_memset (ms_regs ms) (ms_mem ms) md).
apply (HMS cx 3 ly S (c_U cx) W (ms_regs ms) (ms_mem ms) md Hb).
destruct HE as (_ & HE33 & HE46 & _).
exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
split; [exact (cno_mframe_of_st cx E ss W ms md 3 ly S (c_U cx) a e16 HS HJ HARU Hh R2 R8 R9 R18 R19 R3 R4 U8 U19 U9
  HE33 HE46 E16 HF64 E48 HA H0 H1 H3 Hr1 Hr3)|].
split; [exact Hab|].
do 8 (split; [assumption|]).
split; [exact Hza|]. split; [exact Hzb|]. split; [exact Hzt | exact Hg].
Qed.

(* ---- from M: `beqz a0` (0x81320; t <> 0), `beqz s6` (0x81328: len = 0 skips the copy), __asan_memcpy (0x81338), the
   run to the memset call ---- *)
Lemma cno_seg_M : cno_at B PC_memset INV_MS -> cno_from B ss_M INV_M.
Proof.
intros HMS cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & -> & -> & Hab & Ha0 & Ha16 & Hb0 & Hb16 & Ht0 & (C2 & C8 & C9 & C18 & C19 & C3 & C4) & E48
  & E49 & E50 & E10 & E20 & E22 & E23 & E24 & E25 & E26 & Hza & Hzb & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & Hsrc0 & _ & Hblk0 & Hmax & _).
assert (Hn0 : 0 <= cno_n cx <= PRESET_FILE_MAX_BYTES) by (unfold cno_n in *; lia).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : cno_F cx = frame_addr ly3 1 (c_fpos cx)) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite <- EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite C19; unfold w64; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HbIn : In (b, cno_n cx + 18) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
assert (HtIn : In (t, cno_n cx + 18) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; right; right; left; reflexivity).
destruct (fsw_ablock_low B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t _ HAR HtIn) as (Lt1 & Lt2 & Lt3).
destruct (fsw_ablock_low B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 a _ HAR HaIn) as (La1 & La2 & La3).
assert (Hn64 : 0 <= cno_n cx < 2 ^ 64) by lia.
(* 0x81320: t <> 0 *)
eapply (SRr_sym_branch tfibsegs W3 E ss_M ms3 md3 (cno_post B cx) BC_EQ (SOff 10 0) (SLit 0) HS); intros Hbr HS1.
{ exfalso. cbn [branch_taken] in Hbr. rewrite fsw_SOff0, E10 in Hbr. cbn [sv_denot] in Hbr.
  rewrite bv_eqb_unsigned in Hbr. unfold w64 in Hbr. rewrite !wz in Hbr by lia. apply Z.eqb_eq in Hbr. lia. }
(* the keep of a block's bytes through a run from a boundary state *)
assert (KZ : forall E0 r csF cssl (m m' : word -> option byte) md0 p (l : list Z),
  bv_unsigned (ew E0 8) = cno_sp0 cx -> bv_unsigned (ew E0 9) = cno_sp1 cx ->
  bv_unsigned (ew E0 19) = cno_F cx -> bv_unsigned (ew E0 18) = cno_SF cx ->
  frame_of E0 (ss_mem (cno_ss r 19 18 csF cssl)) m m' ->
  In (p, cno_n cx + 18) (ablocks B ly3 S3) -> Z.of_nat (length l) <= cno_n cx + 18 -> zbytes_at tfibsegs W3 m p l ->
  ARU tfibsegs B ly3 S3 (c_U cx) W3 m md0 -> zbytes_at tfibsegs W3 m' p l).
{ intros E0 r csF cssl m m' md0 p l V8 V9 V19 V18 HF Hp Hl Hz HARUm.
  destruct (cno_run_keeps B cx E0 r csF cssl ly3 S3 (c_U cx) W3 m md0 m m' Hb HARUm Hin EF V8 V9 V19 V18 HF) as (_ & KB).
  apply (cno_zbytes_kept W3 W3 m m' p _); [|exact Hz].
  intros j Hj.
  pose proof (req_size_pos (cno_n cx + 18) ltac:(lia)) as Hrq.
  exact (aview_at tfibsegs (w_H W3) m' m (p + j) (KB p _ j Hp ltac:(lia))). }
assert (KG : forall E0 r csF cssl (m m' : word -> option byte) md0,
  bv_unsigned (ew E0 8) = cno_sp0 cx -> bv_unsigned (ew E0 9) = cno_sp1 cx ->
  bv_unsigned (ew E0 19) = cno_F cx -> bv_unsigned (ew E0 18) = cno_SF cx ->
  frame_of E0 (ss_mem (cno_ss r 19 18 csF cssl)) m m' ->
  ARU tfibsegs B ly3 S3 (c_U cx) W3 m md0 ->
  fs_glob tfibsegs W3 m (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) ->
  fs_glob tfibsegs W3 m' (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
{ intros E0 r csF cssl m m' md0 V8 V9 V19 V18 HF HARUm Hgm.
  destruct (cno_run_keeps B cx E0 r csF cssl ly3 S3 (c_U cx) W3 m md0 m m' Hb HARUm Hin EF V8 V9 V19 V18 HF) as (KL & _).
  apply (cno_glob_ledger W3 W3 m m' _ _ _ _); [|exact Hgm].
  intros y Hy. exact (aview_at tfibsegs (w_H W3) m' m y (KL y Hy)). }
destruct HE as (HE32 & HE33 & HE46 & HE47).
lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  eapply (SRr_sym_branch tfibsegs W3 E ss ms3 md3 (cno_post B cx) BC_EQ (SOff 22 0) (SLit 0) HS1) end;
  intros Hbr2 HS2.
- (* len = 0: no copy *)
  assert (Hn : cno_n cx = 0).
  { cbn [branch_taken] in Hbr2. rewrite fsw_SOff0, E22 in Hbr2. cbn [sv_denot] in Hbr2.
    rewrite bv_eqb_unsigned in Hbr2. unfold w64 in Hbr2. rewrite !wz in Hbr2 by lia. apply Z.eqb_eq in Hbr2. lia. }
  pose proof HARU as HARU0.
  fsw_aj_run_toU cno_tbl_ok HS2 HJ HARU PC_memset.
  { eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); clear - FS N4; lia. }
  apply (cno_MS_of cx E _ W3 ms _ ly3 S3 a b t (SOff 26 0) HMS Hb (conj HE32 (conj HE33 (conj HE46 HE47))) HS2
    ltac:(vm_compute; reflexivity) eq_refl HJ HARU Hh Hab).
  + rewrite (cno_reg _ E _ ms 2%bv 2 HS2 ltac:(vm_compute; reflexivity)); exact C2.
  + rewrite (cno_reg _ E _ ms 8%bv 8 HS2 ltac:(vm_compute; reflexivity)); exact C8.
  + rewrite (cno_reg _ E _ ms 9%bv 9 HS2 ltac:(vm_compute; reflexivity)); exact C9.
  + rewrite (cno_reg _ E _ ms 18%bv 18 HS2 ltac:(vm_compute; reflexivity)); exact C18.
  + rewrite (cno_reg _ E _ ms 19%bv 19 HS2 ltac:(vm_compute; reflexivity)); exact C19.
  + rewrite (cno_reg _ E _ ms 3%bv 3 HS2 ltac:(vm_compute; reflexivity)); exact C3.
  + rewrite (cno_reg _ E _ ms 4%bv 4 HS2 ltac:(vm_compute; reflexivity)); exact C4.
  + exact (fsw_reg_lit (w_H W3) E _ ms 1%bv 0x81358 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
  + rewrite (cno_reg_add (w_H W3) E _ ms 10%bv 10 0 22 0 t (cno_n cx) HS2 ltac:(vm_compute; reflexivity) E10 E22
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
  + exact (fsw_reg_lit (w_H W3) E _ ms 11%bv 0 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
  + exact (fsw_reg_lit (w_H W3) E _ ms 12%bv 17 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
  + rewrite (cno_reg _ E _ ms 20%bv 20 HS2 ltac:(vm_compute; reflexivity)); exact E20.
  + rewrite (cno_reg _ E _ ms 21%bv 10 HS2 ltac:(vm_compute; reflexivity)); exact E10.
  + rewrite (cno_reg_add (w_H W3) E _ ms 22%bv 10 (-1) 24 0 t (cno_n cx + 18) HS2 ltac:(vm_compute; reflexivity) E10 E24
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
  + rewrite (cno_reg _ E _ ms 25%bv 25 HS2 ltac:(vm_compute; reflexivity)); exact E25.
  + exact U8.
  + exact U19.
  + exact U9.
  + rewrite fsw_SOff0. exact E26.
  + exact HF64.
  + exact E48.
  + lia.
  + vm_compute. reflexivity.
  + intros r1 Hr. vm_compute in Hr. injection Hr as <-. split; [reflexivity | cno_inc].
  + intros r3 Hr. vm_compute in Hr. injection Hr as <-. split; [reflexivity | split; cno_inc].
  + lazymatch goal with |- exists r, nth_error ?L 1 = Some r =>
      destruct (nth_error L 1) as [r|] eqn:Eq; [exists r; reflexivity | vm_compute in Eq; discriminate Eq] end.
  + lazymatch goal with |- exists r, nth_error ?L 3 = Some r =>
      destruct (nth_error L 3) as [r|] eqn:Eq; [exists r; reflexivity | vm_compute in Eq; discriminate Eq] end.
  + exact (KZ E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 a (pn_copy (c_db cx) 65) U8 U9 U19 U18 HF HaIn
      ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hza HARU0).
  + exact (KZ E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 b (pn_copy (c_db cx) 66) U8 U9 U19 U18 HF HbIn
      ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hzb HARU0).
  + assert (Hdb : c_db cx = []) by (destruct (c_db cx) as [|z l] eqn:Edb; [reflexivity|];
      unfold cno_n in Hn; rewrite Edb in Hn; cbn [length] in Hn; lia).
    rewrite Hdb. intros j Hj. cbn [length] in Hj. lia.
  + exact (KG E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 U8 U9 U19 U18 HF HARU0 Hg).
- (* len > 0: __asan_memcpy (t, d, len) *)
  assert (Hnp : 0 < cno_n cx).
  { cbn [branch_taken] in Hbr2. rewrite fsw_SOff0, E22 in Hbr2. cbn [sv_denot] in Hbr2.
    rewrite bv_eqb_unsigned in Hbr2. unfold w64 in Hbr2. rewrite !wz in Hbr2 by lia. apply Z.eqb_neq in Hbr2. lia. }
  pose proof HARU as HARU0.
  fsw_aj_run_toU cno_tbl_ok HS2 HJ HARU PC_memcpy.
  { eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ U8 U19 U18 U9 EFa); clear - FS N4; lia. }
  pose proof (KZ E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 a (pn_copy (c_db cx) 65) U8 U9 U19 U18 HF HaIn
    ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hza HARU0) as Hza1.
  pose proof (KZ E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 b (pn_copy (c_db cx) 66) U8 U9 U19 U18 HF HbIn
    ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hzb HARU0) as Hzb1.
  pose proof (KG E 0x81320 cno_flag_chunk cno_sl18 _ _ md3 U8 U9 U19 U18 HF HARU0 Hg) as Hg1.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  lazymatch type of HS2 with st_ok _ _ ?ss _ => set (ssR := ss) in HS2 end.
  assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg _ E _ ms 2%bv 2 HS2 ltac:(vm_compute; reflexivity)); exact C2).
  assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
    by (rewrite (cno_reg _ E _ ms 8%bv 8 HS2 ltac:(vm_compute; reflexivity)); exact C8).
  assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg _ E _ ms 9%bv 9 HS2 ltac:(vm_compute; reflexivity)); exact C9).
  assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
    by (rewrite (cno_reg _ E _ ms 3%bv 3 HS2 ltac:(vm_compute; reflexivity)); exact C3).
  assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
    by (rewrite (cno_reg _ E _ ms 4%bv 4 HS2 ltac:(vm_compute; reflexivity)); exact C4).
  assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
    by (rewrite (cno_reg _ E _ ms 18%bv 18 HS2 ltac:(vm_compute; reflexivity)); exact C18).
  assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
    by (rewrite (cno_reg _ E _ ms 19%bv 19 HS2 ltac:(vm_compute; reflexivity)); exact C19).
  assert (R10 : getr (ms_regs ms) 10 = w64 t)
    by (rewrite (cno_reg _ E _ ms 10%bv 10 HS2 ltac:(vm_compute; reflexivity)); exact E10).
  assert (R11 : getr (ms_regs ms) 11 = w64 (c_d cx))
    by (rewrite (cno_reg _ E _ ms 11%bv 23 HS2 ltac:(vm_compute; reflexivity)); exact E23).
  assert (R12 : getr (ms_regs ms) 12 = w64 (cno_n cx))
    by (rewrite (cno_reg _ E _ ms 12%bv 22 HS2 ltac:(vm_compute; reflexivity)); exact E22).
  assert (R20 : getr (ms_regs ms) 20 = w64 b)
    by (rewrite (cno_reg _ E _ ms 20%bv 20 HS2 ltac:(vm_compute; reflexivity)); exact E20).
  assert (R21 : getr (ms_regs ms) 21 = w64 t)
    by (rewrite (cno_reg _ E _ ms 21%bv 10 HS2 ltac:(vm_compute; reflexivity)); exact E10).
  assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
    by (rewrite (cno_reg _ E _ ms 22%bv 22 HS2 ltac:(vm_compute; reflexivity)); exact E22).
  assert (R24 : getr (ms_regs ms) 24 = w64 (cno_n cx + 18))
    by (rewrite (cno_reg _ E _ ms 24%bv 24 HS2 ltac:(vm_compute; reflexivity)); exact E24).
  assert (R25 : getr (ms_regs ms) 25 = w64 SHADOW_OFF)
    by (rewrite (cno_reg _ E _ ms 25%bv 25 HS2 ltac:(vm_compute; reflexivity)); exact E25).
  assert (R26 : getr (ms_regs ms) 26 = w64 (cno_F cx))
    by (rewrite (cno_reg _ E _ ms 26%bv 26 HS2 ltac:(vm_compute; reflexivity)); exact E26).
  assert (R1 : getr (ms_regs ms) 1 = w64 0x8133c)
    by exact (fsw_reg_lit (w_H W3) E ssR ms 1%bv 0x8133c HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
  assert (Hsite : cno_site B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4)
    by exact (cno_site_of B cx E ssR W3 ms 3 ly3 S3 (c_U cx) md4 0x8133c (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS2
      ltac:(vm_compute; reflexivity) HJ HARU Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
  pose (rF := match nth_error (ss_mem ssR) 1 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
  assert (HcF : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
    (YP09.mkChunk 120 (CVal 8 (SOff 46 0)))).
  { apply (cno_chunk_at E ssR (w_H W3) ms 1 rF 19 _ HS2); [vm_compute; reflexivity | vm_compute; reflexivity | cno_inc]. }
  pose (rL := match nth_error (ss_mem ssR) 3 with Some x => x | None => YP09.mkRegion None 0 0 0 0 [] end).
  assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
    (YP09.mkChunk 24 (CVal 8 (SOff 48 0)))).
  { apply (cno_chunk_at E ssR (w_H W3) ms 3 rL 9 _ HS2); [vm_compute; reflexivity | vm_compute; reflexivity | cno_inc]. }
  rewrite U19 in HcF. rewrite U9 in HcL.
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t _ 1 (c_fpos cx) HAR HtIn Hin)
    as Htf.
  rewrite <- EFa in Htf. change (fs_frame_bytes 1) with 128 in Htf. unfold zdisjoint in Htf. cbn [fst snd] in Htf.
  (* the call *)
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssR ms HS2 eq_refl).
  replace (ss_pc ssR) with PC_memcpy by (vm_compute; reflexivity).
  change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (seg_rom tfibsegs)) md4)
    with (cfg_at tfibsegs PC_memcpy (ms_regs ms) (ms_mem ms) md4).
  eapply SRr_bind.
  { exact (cno_call_mcpy cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 t Hb Hsite eq_refl R1 R10 R11 R12 Hnp
      (ex_intro _ [(a, cno_n cx + 18); (b, cno_n cx + 18)] Hab)). }
  cbv beta. intros W' c' _ Hret.
  set (xs := fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t).
  destruct (cno_resume B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms) md4 0 (c_U cx)
    (fun a0 => t <= a0 < t + cno_n cx) _ W' c' xs cno_flag_chunk cno_sl18 Hb Hsite Hret R9 R18 R19)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ' & HARU' & Hh' & HP & HBK & HZ & HPP & HS').
  + intros y Hy Hk. lia.
  + vm_compute. reflexivity.
  + intros regs'. apply (proj2 (proj2 (cno_saved_of_st cx E ssR W3 ms (conj HE32 (conj HE33 (conj HE46 HE47))) U8 HS2
      ltac:(vm_compute; reflexivity)))).
    intros j Hj. destruct (cno_E_env cx regs' a b t) as (_ & HX & _). exact (eq_trans (HX j Hj) (eq_sym (HE33 j Hj))).
  + constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi Hk. lia.
  + constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi Hk. lia.
  + intros regs' _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E _ _ _ _ _ _ _ HcF). rewrite !fsw_SOff0.
    destruct (cno_E_env cx regs' a b t) as (_ & _ & X46 & _). exact (eq_trans X46 (eq_sym HE46)).
  + intros regs' _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E48.
    unfold xs. change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
  + cbv beta in HPP. destruct HPP as (-> & -> & -> & Ea0 & Hzt & Hout).
    assert (Era : raZ (ms_regs ms) = 0x8133c) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
    rewrite Era in Ec, HS'. subst c'.
    set (E' := Ereg regs' xs) in *.
    assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
      ew E' n = getr (ms_regs ms) r).
    { intros r n Hn' Hc. subst E'. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
    assert (V8 : bv_unsigned (ew E' 8) = cno_sp0 cx) by (rewrite (KR 8%bv 8%nat eq_refl ltac:(cno_cs)), R8; apply wz; lia).
    assert (V9 : bv_unsigned (ew E' 9) = cno_sp1 cx) by (rewrite (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), R9; apply wz; lia).
    assert (V19 : bv_unsigned (ew E' 19) = cno_F cx) by (rewrite (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), R19; apply wz; lia).
    assert (V18 : bv_unsigned (ew E' 18) = cno_SF cx)
      by (rewrite (KR 18%bv 18%nat eq_refl ltac:(cno_cs)), R18; apply wz; unfold cno_SF, kHighShadowEnd in *; lia).
    assert (HE' : cno_E cx E') by exact (cno_E_env cx regs' a b t).
    (* the ledger and a / b: kept by the copy *)
    destruct (al_blocks tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t _ HAR HtIn)
      as (_ & _ & _ & _ & _ & Hpw & _).
    rewrite Hab, map_app in Hpw. apply pairwise_app_l in Hpw as (_ & Hpw0).
    cbn [cno_raw map pairwise fst snd] in Hpw0.
    destruct Hpw0 as (HFa & HFb & _). apply Forall_cons_iff in HFa as (Dab & HFa).
    apply Forall_cons_iff in HFa as (Dat & _). apply Forall_cons_iff in HFb as (Dbt & _).
    unfold zdisjoint in Dab, Dat, Dbt. cbn [fst snd] in Dab, Dat, Dbt.
    destruct (fsw_ablock_low B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 b _ HAR HbIn) as (Lb1 & Lb2 & Lb3).
    pose proof (fsw_ablock_off_img B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t _ HAR HtIn) as Ltimg.
    assert (KC : forall p l, In (p, cno_n cx + 18) (ablocks B ly3 S3) ->
      (p + req_size (cno_n cx + 18) <= t \/ t + req_size (cno_n cx + 18) <= p) -> Z.of_nat (length l) <= cno_n cx + 18 ->
      zbytes_at tfibsegs W3 (ms_mem ms) p l -> zbytes_at tfibsegs W3 mem' p l).
    { intros p l Hp Hpt Hl Hz. apply (cno_zbytes_kept W3 W3 (ms_mem ms) mem' p _); [|exact Hz].
      pose proof (req_size_pos (cno_n cx + 18) ltac:(lia)) as Hrq.
      destruct (fsw_ablock_low B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 p _ HAR Hp) as (Lp1 & Lp2 & Lp3).
      intros j Hj. exact (HBK p _ j Hp Hp ltac:(lia) ltac:(cbv beta; lia)). }
    pose proof (KC a (pn_copy (c_db cx) 65) HaIn ltac:(lia) ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hza1) as Hza2.
    pose proof (KC b (pn_copy (c_db cx) 66) HbIn ltac:(lia) ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hzb1) as Hzb2.
    assert (Hg2 : fs_glob tfibsegs W3 mem' (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
    { apply (cno_glob_ledger W3 W3 (ms_mem ms) mem' _ _ _ _); [|exact Hg1].
      intros y Hy. pose proof (cno_pstat_bounds y Hy) as Hyb.
      apply Hout; [lia | unfold FS_IMG_END in *; lia | unfold ESTACK; lia]. }
    (* the run 0x8133c -> the memset call *)
    pose proof HARU' as HARU'0.
    fsw_aj_run_toU cno_tbl_ok HS' HJ' HARU' PC_memset.
    { eapply (cno_awr_ss B E' _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) _ _ _ V8 V19 V18 V9 EFa);
        clear - FS N4; lia. }
    assert (E'48 : ew E' 48 = w64 a) by (subst E'; unfold xs; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity).
    rename ms into msc. rename ms0 into ms.
    apply (cno_MS_of cx E' _ W3 ms _ ly3 S3 a b t (SOff 26 0) HMS Hb HE' HS' ltac:(vm_compute; reflexivity) eq_refl
      HJ' HARU' Hh' Hab).
    * rewrite (cno_reg _ E' _ ms 2%bv 2 HS' ltac:(vm_compute; reflexivity)), (KR 2%bv 2%nat eq_refl ltac:(cno_cs)); exact R2.
    * rewrite (cno_reg _ E' _ ms 8%bv 8 HS' ltac:(vm_compute; reflexivity)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)); exact R8.
    * rewrite (cno_reg _ E' _ ms 9%bv 9 HS' ltac:(vm_compute; reflexivity)), (KR 9%bv 9%nat eq_refl ltac:(cno_cs)); exact R9.
    * rewrite (cno_reg _ E' _ ms 18%bv 18 HS' ltac:(vm_compute; reflexivity)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs));
        exact R18.
    * rewrite (cno_reg _ E' _ ms 19%bv 19 HS' ltac:(vm_compute; reflexivity)), (KR 19%bv 19%nat eq_refl ltac:(cno_cs));
        exact R19.
    * rewrite (cno_reg _ E' _ ms 3%bv 3 HS' ltac:(vm_compute; reflexivity)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)); exact R3.
    * rewrite (cno_reg _ E' _ ms 4%bv 4 HS' ltac:(vm_compute; reflexivity)), (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); exact R4.
    * exact (fsw_reg_lit (w_H W3) E' _ ms 1%bv 0x81358 HS' ltac:(vm_compute; reflexivity) ltac:(lia)).
    * rewrite (cno_reg_add (w_H W3) E' _ ms 10%bv 21 0 22 0 t (cno_n cx) HS' ltac:(vm_compute; reflexivity)
        ltac:(rewrite (KR 21%bv 21%nat eq_refl ltac:(cno_cs)); exact R21)
        ltac:(rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
    * exact (fsw_reg_lit (w_H W3) E' _ ms 11%bv 0 HS' ltac:(vm_compute; reflexivity) ltac:(lia)).
    * exact (fsw_reg_lit (w_H W3) E' _ ms 12%bv 17 HS' ltac:(vm_compute; reflexivity) ltac:(lia)).
    * rewrite (cno_reg _ E' _ ms 20%bv 20 HS' ltac:(vm_compute; reflexivity)), (KR 20%bv 20%nat eq_refl ltac:(cno_cs));
        exact R20.
    * rewrite (cno_reg _ E' _ ms 21%bv 21 HS' ltac:(vm_compute; reflexivity)), (KR 21%bv 21%nat eq_refl ltac:(cno_cs));
        exact R21.
    * rewrite (cno_reg_add (w_H W3) E' _ ms 22%bv 21 (-1) 24 0 t (cno_n cx + 18) HS' ltac:(vm_compute; reflexivity)
        ltac:(rewrite (KR 21%bv 21%nat eq_refl ltac:(cno_cs)); exact R21)
        ltac:(rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
    * rewrite (cno_reg _ E' _ ms 25%bv 25 HS' ltac:(vm_compute; reflexivity)), (KR 25%bv 25%nat eq_refl ltac:(cno_cs));
        exact R25.
    * exact V8.
    * exact V19.
    * exact V9.
    * rewrite fsw_SOff0, (KR 26%bv 26%nat eq_refl ltac:(cno_cs)). exact R26.
    * exact HF64.
    * exact E'48.
    * lia.
    * vm_compute. reflexivity.
    * intros r1 Hr. vm_compute in Hr. injection Hr as <-. split; [reflexivity | cno_inc].
    * intros r3 Hr. vm_compute in Hr. injection Hr as <-. split; [reflexivity | split; cno_inc].
    * lazymatch goal with |- exists r, nth_error ?L 1 = Some r =>
        destruct (nth_error L 1) as [r|] eqn:Eq; [exists r; reflexivity | vm_compute in Eq; discriminate Eq] end.
    * lazymatch goal with |- exists r, nth_error ?L 3 = Some r =>
        destruct (nth_error L 3) as [r|] eqn:Eq; [exists r; reflexivity | vm_compute in Eq; discriminate Eq] end.
    * exact (KZ E' 0x8133c cno_flag_chunk cno_sl18 _ _ _ a (pn_copy (c_db cx) 65) V8 V9 V19 V18 HF0 HaIn
        ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hza2 HARU'0).
    * exact (KZ E' 0x8133c cno_flag_chunk cno_sl18 _ _ _ b (pn_copy (c_db cx) 66) V8 V9 V19 V18 HF0 HbIn
        ltac:(rewrite cno_pn_length; unfold cno_n; lia) Hzb2 HARU'0).
    * exact (KZ E' 0x8133c cno_flag_chunk cno_sl18 _ _ _ t (c_db cx) V8 V9 V19 V18 HF0 HtIn
        ltac:(unfold cno_n; lia) Hzt HARU'0).
    * exact (KG E' 0x8133c cno_flag_chunk cno_sl18 _ _ _ V8 V9 V19 V18 HF0 HARU'0 Hg2).
Qed.
(* ================= the chain: the entry and segment 1, past_nul x2, __wrap_malloc, M (memcpy), MS (memset and the
   inline check), segment D (the decodes, the branches, bcmp x2), segment F (fuzz_free x3, __wrap_free x3), the
   epilogue and the ret (cno_tail_ret) ================= *)
Lemma cno_chain : cno_segD_T B -> cno_segF_T B -> check_no_overread_spec tfibsegs B.
Proof.
intros HD HF. apply cno_enter, cno_seg_P1, cno_seg_P2, cno_seg_M, cno_seg_MS, HD, HF. exact cno_tail_ret.
Qed.
End T.

(* ================= check_no_overread_ok, at the A image's sink (AE2k.tfib_sink_head, passed explicitly) =================
   Section hypotheses: the callee contracts (past_nul, preset_base64_decode, fuzz_free), the runtime contracts
   (__wrap_malloc / __wrap_free, __asan_memcpy / __asan_memset, bcmp, __asan_stack_malloc_1), the image facts and the
   B-cell equations, as every fs walk takes them; every lane's call step is applied as its real lemma. *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis PN : @past_nul_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Hypothesis DEC : @FSH_Fn_writer.decode_spec_ff fx rc AE2k.tfib_sink_head B tfibsegs.
Hypothesis FFREE : @fuzz_free_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1.
Hypothesis ASM1 : astack_malloc_realizesU tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis HMAL : pc_wrap_malloc (as_code B) = PC_malloc.
Hypothesis AMEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Hypothesis ABCMP : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis AFREE : FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis HFRE : pc_wrap_free (as_code B) = PC_free.

Theorem check_no_overread_ok : @check_no_overread_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
apply (@cno_chain fx rc AE2k.tfib_sink_head B); try assumption.
all: first
  [ solve [eapply (@FSW_check_no_overread_mem.cno_call_mal fx rc AE2k.tfib_sink_head B); eassumption]
  | solve [eapply (@FSW_check_no_overread_mem.cno_call_mcpy fx rc AE2k.tfib_sink_head B); eassumption]
  | solve [eapply (@FSW_check_no_overread_mem.cno_call_mset fx rc AE2k.tfib_sink_head B); eassumption]
  | solve [exact (@FSW_check_no_overread_ret.cno_tail_ret fx rc AE2k.tfib_sink_head B)]
  | solve [eapply (@FSW_check_no_overread_segd.cno_segD fx rc AE2k.tfib_sink_head B);
      [eapply (@FSW_check_no_overread_dec.cno_call_dec fx rc AE2k.tfib_sink_head B); eassumption
      | eapply (@FSW_check_no_overread_tail.cno_call_bcmp fx rc AE2k.tfib_sink_head B); eassumption]]
  | solve [eapply (@FSW_check_no_overread_segf.cno_segF fx rc AE2k.tfib_sink_head B);
      [eapply (@FSW_check_no_overread_ffree.cno_call_ffree fx rc AE2k.tfib_sink_head B); eassumption
      | eapply (@FSW_check_no_overread_tail.cno_call_afree fx rc AE2k.tfib_sink_head B); eassumption]] ].
Qed.
End F.

About check_no_overread_ok.
Print Assumptions check_no_overread_ok.
