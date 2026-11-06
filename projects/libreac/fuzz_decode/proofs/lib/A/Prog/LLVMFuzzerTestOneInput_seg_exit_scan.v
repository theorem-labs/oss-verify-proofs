(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module names changed; 344 of its 394 lines of code are new or changed and 2639 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_scan: the scan piece of the exit segment of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, ex_scan_ok : ex_scan_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v).

   The code (DecodeList.v:606-627, map-code.md section 2): from +0x908, where the third reac_upstream_decode refused
   (a0 = -1), `li a2,0; mv a3,s7; mv a1,s7`, then the scan loop L6 (+0x914 .. +0x940) over the upstream buffer
   (s7 = upb, s8 = its length, counting down): the shadow check of the byte at a1 (`srli/add s2/lb/bnez`, slow path
   +0x948 .. +0x954), `lbu a4,0(a3)`, `a2 |= (a4 != 0xa5)`, a1 and a3 one up, s8 one down, `bnez s8` back to +0x914;
   on exit `j +0x958`, `bnez a2` to the abort at +0xa4c, `blez a0` to +0x98c.

   How it is proved. The loop is a well-founded induction on the bytes left (sc_loop). At the loop head +0x914 the
   concrete invariant sc_inv says: a1 = a3 = upb + i, s8 = len - i, a2 = 0, a0 = -1, s2 = the shadow base, the
   frame registers and the journal as at +0x908, and the buffer still holds the 0xa5 fill (dec_a_filled). Each
   iteration seats a fresh symbolic state ss_it (registers as atoms of their own values; a1's atom 11 carries the
   shadow entry of the one byte at upb + i, from AR's block law for (upb, len); a3's atom 13 the read-only region
   holding that byte, 0xa5), runs it with the token engine (the shadow check takes the fast path: the `andi` form
   slow block's 1-byte obligation is covered by the entry, so no obligation is left) up to the back edge, and
   splits on `bnez s8`: taken, one more step reaches +0x914 with the invariant at i + 1; not taken (s8 = 0), the
   run goes on through +0x944 / +0x958 / +0x95c to +0x98c, the two exit branches decided by the engine itself
   (a2 is the literal 0: every byte read is 0xa5, so the abort edge +0x958 is refuted; a0 is the literal -1, so
   `blez a0` is taken). Nothing is stored: every region is read-only, so the memory after each run agrees with the
   one before at every address (sc_frame_ro) and dec_a_core is carried over by sc_core_pt with the run's journal.
   At +0x98c the events (dec_ev_86c) and the meter are those of +0x908, weakened to ex_st_98c's bounds with
   dec_crt_cost_max >= 0 (mo_malloc_nonneg / mo_free_nonneg, mo_le_mono, mo_ok_le).

   Steps follow libreac/fuzz_boxreg's ReadName.v (pb_read_name, 1d92330b7ad: the entry sstate, paj_run_tok,
   psrr_branch_tok, shent_ok_of_range, range_addressable_of_block) and this unit's LLVMFuzzerTestOneInput_seg_entry.v
   (a Theorem Labs lane, 4d4ce59e5f2: EEN / reg_at / the dec_a_core build). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  DecodeSyms DecodeList DecodeAddr DecodePa DecodePaLib DecodeImg YC4b YC1g YC1h YC81.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                               *)
(* ------------------------------------------------------------------ *)

(* At +0x914 (offset 2324), iteration i: every register is the atom of its own value, but a0 and a2 are pinned to
   the literals -1 and 0; atom 18 (s2) is the shadow base; atom 11 (a1, which the shadow check reads) and atom 13
   (a3, which the load reads) are both upb + i; the byte at a3 is a read-only region holding the fill. *)
Definition sc_reg : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit DEC_FILL))].
Definition sc_facts : facts := mkFacts [(18%nat, mkAF SB SB 0); (11%nat, PTR 0); (13%nat, PTR 0)] [] [].
Definition sc_regs : list sv := sr_set (sr_set sr_atoms 10%bv (SLit (-1))) 12%bv (SLit 0).
Definition ss_it : sstate := mkSS 2324 sc_regs [sc_reg] None sc_facts.
(* The shadow entry of the byte at a1. *)
Definition sc_SH : list shent := [mkSHE 11 0 1].
(* At +0x908 (offset 2312): the registers as atoms, the shadow base in atom 18; no region (the three moves read
   nothing). *)
Definition ss_908 : sstate := mkSS 2312 sr_atoms [] None (mkFacts [(18%nat, mkAF SB SB 0)] [] []).

(* A read-only region list: the run's memory agrees with the old one at every address. *)
Lemma sc_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
(* The write rights of read-only regions. *)
Ltac sc_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
(* The model term after a run, named and opaque (it doubles at every run otherwise). *)
Ltac sc_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.
(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac sc_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac sc_kin := cbn [In]; repeat (first [left; reflexivity | right]).
(* A register the run kept: KR (regs_kept_of_st_ok_pi), then the hypothesis that gives its old value. *)
Ltac sc_keep KR := etransitivity; [apply KR; sc_kin | eassumption].
(* The memory after a run of read-only regions agrees with the one before (closed region list for vm_compute). *)
Ltac sc_km HF KM :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m0 ?m1 =>
    pose proof (sc_frame_ro Ex rs m0 m1 ltac:(vm_compute; reflexivity) HF) as KM end.

Lemma sc_uolen_pos : forall cx, 1 <= ex_uolen cx.
Proof.
intros cx. unfold ex_uolen, dec_a_uolen.
lazymatch goal with |- context [0 <? ?x] => destruct (Z.ltb_spec 0 x); lia end.
Qed.



Section sc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition sc_E (regs : bvmap 5 word) : env := Eimg (PI := PI_decode) (Ereg regs []).
Lemma sc_pc : forall k, Z_to_bv 64 (BASE + k) = w64 (DEC_A_LLVMF + k).
Proof. intros k. reflexivity. Qed.

(* ---- memories that agree at every address ---- *)
Lemma sc_aview_pt : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) ->
  forall a, aview decodesegs0 H m2 a = aview decodesegs0 H m a.
Proof. intros H m m2 Hpt a. apply aview_eq_of. unfold mrestrict. rewrite (Hpt (Z_to_bv 64 a)). reflexivity. Qed.
Lemma sc_apresent_pt : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) ->
  forall a, apresent H m a -> apresent H m2 a.
Proof. intros H m m2 Hpt a [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb. Qed.
Lemma sc_rdword_pt : forall (r r2 : reader) a, (forall x, r2 x = r x) -> rdword r2 a = rdword r a.
Proof. intros r r2 a Hr. unfold rdword. rewrite !Hr. reflexivity. Qed.
Lemma sc_garr8_pt : forall H (m m2 : word -> option byte) base l, (forall x, m2 x = m x) ->
  garr8 decodesegs0 (mrestrict H m) base l -> garr8 decodesegs0 (mrestrict H m2) base l.
Proof.
intros H m m2 base l Hpt HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite (mbyte_of_aview decodesegs0 H H m m2 _ (sc_aview_pt H m m2 Hpt _)). exact (Hv k Hk).
Qed.
Lemma sc_fsh_pt : forall cx (r r2 : reader) b4 b5, (forall x, r2 x = r x) ->
  dec_a_fsh cx r b4 b5 -> dec_a_fsh cx r2 b4 b5.
Proof.
intros cx r r2 b4 b5 Hr (F1 & F2 & F3 & F4). unfold dec_a_fsh.
split; [intros i Hi; rewrite Hr; exact (F1 i Hi)|]. split; [rewrite Hr; exact F2|]. split; [rewrite Hr; exact F3|].
intros i Hi; rewrite Hr; exact (F4 i Hi).
Qed.
(* dec_a_core is kept by a stretch that writes no memory and none of s0, s1, sp, gp, tp, given its journal. *)
Lemma sc_core_pt : forall B cx ly S (W : world decodesegs0) regs mem md regs2 mem2 md2 k,
  dec_a_core B cx ly S W regs mem md k ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 k ->
  (forall x, mem2 x = mem x) ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_a_core B cx ly S W regs2 mem2 md2 k.
Proof.
intros B cx ly S W regs mem md regs2 mem2 md2 k
  (_ & Hfrs & R8 & R9 & Rsp & Hsp & Hal & R3 & R4 & Hsv & HF1 & HF2 & Hfp & Hfl & Hpay & Hga) HJ Hpt E2 E3 E4 E8 E9.
unfold dec_a_core.
split; [exact HJ|]. split; [exact Hfrs|]. split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split; [unfold spZ; rewrite E2; exact Rsp|]. split; [exact Hsp|]. split; [exact Hal|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split.
{ unfold dec_a_saved in *. eapply Forall_impl; [|exact Hsv]. intros o Ho.
  rewrite (sc_rdword_pt _ _ _ (sc_aview_pt _ _ _ Hpt)). exact Ho. }
split; [exact HF1|]. split; [exact HF2|].
split; [intros a Ha; apply (sc_apresent_pt _ _ _ Hpt); apply Hfp; exact Ha|].
split; [rewrite (sc_rdword_pt _ _ _ (sc_aview_pt _ _ _ Hpt)); exact Hfl|].
split; [exact Hpay|].
exact (sc_garr8_pt _ _ _ _ _ Hpt Hga).
Qed.

(* ReadName.v rn_val_mem1: a byte of the view as a one-byte value. *)
Lemma sc_val_mem1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (kk = 0%nat) as -> by lia.
destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr).
change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hb.
rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the two entry states ---- *)
Lemma sc_entry_908 : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  YK11.getr regs 18 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (sc_E regs) ss_908
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 2312)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem H18.
assert (U18 : bv_unsigned (ew (sc_E regs) 18) = SHADOW_OFF).
{ unfold sc_E. rewrite (ew_Eimg_Ereg_nat regs [] 18 18%bv eq_refl), H18. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
unfold ss_908. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, Z.pow_0_r, Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

Lemma sc_entry_it : forall B (LAWS : AR_laws SEGS B) ly S (W : world SEGS) (regs : bvmap 5 word) mem md upb n i,
  AR SEGS B ly S W mem md -> In (upb, n) (ablocks B ly S) -> 0 <= i < n ->
  YK11.getr regs 10 = w64 (-1) -> YK11.getr regs 12 = w64 0 -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 11 = w64 (upb + i) -> YK11.getr regs 13 = w64 (upb + i) ->
  aview SEGS (w_H W) mem (upb + i) = Some DEC_FILL ->
  st_ok_pi SEGS VAL (sc_E regs) ss_it
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 2324)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff 18 0) sc_SH (sc_E regs) (mrestrict (w_H W) mem).
Proof.
intros B LAWS ly S W regs mem md upb n i HAR Hin Hi H10 H12 H18 H11 H13 Hfill.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof (req_size_pos0 n ltac:(lia)) as Hreq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (sc_E regs) nn = YK11.getr regs r)
  by (intros nn r Hn; unfold sc_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U11 : bv_unsigned (ew (sc_E regs) 11) = upb + i)
  by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew (sc_E regs) 13) = upb + i)
  by (rewrite (EE 13%nat 13%bv eq_refl), H13; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (sc_E regs) 18) = SHADOW_OFF)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- unfold ss_it, sc_regs.
  apply (st_ok_pi_pin_reg' (sc_E regs) (mkSS 2324 (sr_set sr_atoms 10%bv (SLit (-1))) [sc_reg] None sc_facts) _ 12%bv 0);
    [| cbn [ms_regs restrict YK11.mkst]; exact H12 | reflexivity].
  apply (st_ok_pi_pin_reg' (sc_E regs) (mkSS 2324 sr_atoms [sc_reg] None sc_facts) _ 10%bv (-1));
    [| cbn [ms_regs restrict YK11.mkst]; exact H10 | reflexivity].
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold sc_reg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (sc_E regs) _ (upb + i) 0 1 (SLit DEC_FILL) DEC_FILL);
      [reflexivity | unfold DEC_FILL; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (sc_val_mem1 _ _ _ _ Hfill).
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [sc_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U11, U13, !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    repeat split; try exact I; lia.
- unfold sh_ok, sc_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem (sc_E regs) (SOff 18 0) 11 (upb + i) 1 (upb + i) 0 1).
  + eapply (range_addressable_of_block SEGS B LAWS ly S W mem md upb n (upb + i) 1 HAR Hin); lia.
  + apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia].
  + apply U_atom; [rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
Qed.

(* ---- the loop ---- *)
(* The state at the loop head +0x914 before iteration i. *)
Definition sc_inv (B : asyms) (cx : dctx) (ly : alayout) (S : astate) (W : world decodesegs0) (res upb i : Z)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  dec_a_core B cx ly S W regs mem md dec_ev_86c /\ dec_a_fr cx regs /\
  YK11.getr regs 10 = w64 (-1) /\ YK11.getr regs 18 = w64 SHADOW_OFF /\
  YK11.getr regs 20 = w64 res /\ YK11.getr regs 23 = w64 upb /\
  YK11.getr regs 24 = w64 (ex_uolen cx - i) /\
  YK11.getr regs 11 = w64 (upb + i) /\ YK11.getr regs 13 = w64 (upb + i) /\ YK11.getr regs 12 = w64 0 /\
  dec_a_filled W mem upb (ex_uolen cx) /\ dec_a_fsh cx (aview decodesegs0 (w_H W) mem) 0 4.

Lemma sc_loop : forall B (LAWS : AR_laws decodesegs0 B) cx (W : world decodesegs0) ly S res upb
  (Q : world decodesegs0 -> config -> Prop),
  Permutation (ablocks B ly S) (ex_blocks B cx res upb) ->
  (forall regs mem md, dec_a_core B cx ly S W regs mem md dec_ev_86c -> dec_a_fr cx regs ->
     YK11.getr regs 20 = w64 res -> YK11.getr regs 23 = w64 upb -> dec_a_fsh cx (aview decodesegs0 (w_H W) mem) 0 4 ->
     Q W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x98c)) mem (YK11.seg_rom decodesegs0)) md)) ->
  forall (m : nat) i regs mem md, Z.of_nat m = ex_uolen cx - i -> 0 <= i < ex_uolen cx ->
  sc_inv B cx ly S W res upb i regs mem md ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x914)) mem (YK11.seg_rom decodesegs0)) md) Q.
Proof.
intros B LAWS cx W ly S res upb Q Hperm Hk.
assert (Hin : In (upb, ex_uolen cx) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). unfold ex_blocks.
  apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
pose proof (paj_run (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_decode)) as BR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
intros m. induction m as [|m IH]; intros i regs mem md Hm Hi Hinv; [lia|].
destruct Hinv as (Hcore & Hfr & R10 & R18 & R20 & R23 & R24 & R11 & R13 & R12 & Hfill & Hfsh).
pose proof Hcore as (HJ & _).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof (req_size_pos0 (ex_uolen cx) ltac:(lia)) as Hreq.
destruct (sc_entry_it B LAWS ly S W regs mem md upb (ex_uolen cx) i HAR Hin Hi R10 R12 R18 R11 R13 (Hfill i Hi))
  as [HS SHOK].
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM (sc_E regs)) by apply Eimg_env.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (sc_E regs) nn = YK11.getr regs r)
  by (intros nn r Hn; unfold sc_E; apply ew_Eimg_Ereg_nat; exact Hn).
change (SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 2324)) mem (YK11.seg_rom SEGS)) md) Q).
clear HAR.
(* +0x914 .. +0x940: the shadow check (fast path), the load, the accumulator, up to the back edge. *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ sc_awr. }
sc_md.
sc_km HF KM1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG1 : forall n, (n < 512)%nat -> ew Ex n = ew (sc_E regs) n)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* `bnez s8` taken: one more step to +0x914, the invariant at i + 1. *)
  assert (Hlt : i + 1 < ex_uolen cx).
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 24 (ex_uolen cx - i) (-1)) in Hc;
      [| rewrite (AG1 24%nat) by lia; rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia | lia].
    rewrite U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 2324.
  { sc_awr. }
  sc_md.
  sc_km HF KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG : forall n, (n < 512)%nat -> ew Ex n = ew (sc_E regs) n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    assert (HAE : env_agree 32 (Ereg regs []) Ex)
      by (split; [intros nn Hnn; rewrite (AG nn) by lia; unfold sc_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs []
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR;
    assert (Hpt : forall x, ms_mem msx x = mem x) by (intros x; rewrite KM2, KM1; reflexivity)
  end.
  sc_reg_at HS (10%bv : bv 5) (w64 (-1)) Q10 ltac:(reflexivity).
  sc_reg_at HS (12%bv : bv 5) (w64 0) Q12 ltac:(reflexivity).
  sc_reg_at HS (11%bv : bv 5) (w64 (upb + (i + 1))) Q11
    ltac:(cbn [sv_denot]; rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl), R11; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  sc_reg_at HS (13%bv : bv 5) (w64 (upb + (i + 1))) Q13
    ltac:(cbn [sv_denot]; rewrite (AG 13%nat) by lia; rewrite (EE 13%nat 13%bv eq_refl), R13; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  sc_reg_at HS (24%bv : bv 5) (w64 (ex_uolen cx - (i + 1))) Q24
    ltac:(cbn [sv_denot]; rewrite (AG 24%nat) by lia; rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  destruct Hfr as (F19 & F21 & F27).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H W) ?msx) =>
    assert (Hinv : sc_inv B cx ly S W res upb (i + 1) (ms_regs msx) (ms_mem msx) mdv0);
    [ split; [apply (sc_core_pt B cx ly S W regs mem md (ms_regs msx) (ms_mem msx) mdv0 dec_ev_86c Hcore HJ Hpt);
              apply KR; sc_kin|];
      split; [split; [sc_keep KR|]; split; sc_keep KR|];
      split; [exact Q10|]; split; [sc_keep KR|]; split; [sc_keep KR|]; split; [sc_keep KR|];
      split; [exact Q24|]; split; [exact Q11|]; split; [exact Q13|]; split; [exact Q12|];
      split; [intros j Hj; rewrite (sc_aview_pt _ _ _ Hpt); exact (Hfill j Hj)|];
      exact (sc_fsh_pt cx _ _ 0 4 (sc_aview_pt _ _ _ Hpt) Hfsh)
    | ] end.
  pmkst HS. rewrite sc_pc.
  apply (IH (i + 1)); [lia | lia | exact Hinv].
- (* `bnez s8` not taken (s8 = 0): +0x944 `j`, +0x958 `bnez a2` (a2 = 0), +0x95c `blez a0` (a0 = -1), +0x98c. *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 2444.
  { sc_awr. }
  sc_md.
  sc_km HF KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG : forall n, (n < 512)%nat -> ew Ex n = ew (sc_E regs) n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    assert (HAE : env_agree 32 (Ereg regs []) Ex)
      by (split; [intros nn Hnn; rewrite (AG nn) by lia; unfold sc_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs []
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 23%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR;
    assert (Hpt : forall x, ms_mem msx x = mem x) by (intros x; rewrite KM2, KM1; reflexivity);
    pmkst HS; rewrite sc_pc; apply SRr_ret;
    apply (Hk (ms_regs msx) (ms_mem msx) mdv0)
  end.
  + apply (sc_core_pt B cx ly S W regs mem md _ _ _ dec_ev_86c Hcore HJ Hpt); apply KR; sc_kin.
  + destruct Hfr as (F19 & F21 & F27). split; [sc_keep KR|]. split; sc_keep KR.
  + sc_keep KR.
  + sc_keep KR.
  + exact (sc_fsh_pt cx _ _ 0 4 (sc_aview_pt _ _ _ Hpt) Hfsh).
Qed.
End sc.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
(* lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v Section cuts, variable for variable. *)
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem ex_scan_ok :
  ex_scan_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_scan_stmt.
intros LAWS _ MTL cx W c _ _ H908.
destruct H908 as (fx' & ly' & S' & regs & mem & md & res & upb & -> & Hfrm & Hcore & Hperm & Hres & Hupb & Hmle & Hmok
  & Hfr & R10 & R18 & R20 & R23 & R24 & Hfill & Hfsh).
pose proof Hcore as (HJ & _).
pose proof (sc_uolen_pos cx) as Hu1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (upb, ex_uolen cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym Hperm)). unfold ex_blocks.
  apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin) as (_ & H4096 & Hceil & _).
pose proof (req_size_pos0 (ex_uolen cx) ltac:(lia)) as Hreq.
pose proof (paj_run_to (fx := fx') (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (sc_entry_908 (fx := fx') W regs mem R18) as HS.
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM (sc_E regs)) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ decode_listing PI_decode) (SOff 18 0) (@nil shent) (sc_E regs) (mrestrict (w_H W) mem))
  by constructor.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (sc_E regs) nn = YK11.getr regs r)
  by (intros nn r Hn; unfold sc_E; apply ew_Eimg_Ereg_nat; exact Hn).
change (SRr (@pa_segs _ decode_listing PI_decode) W
  (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 2312)) mem
    (YK11.seg_rom (@pa_segs _ decode_listing PI_decode))) md) (ex_st_98c B MT cx)).
(* +0x908 .. +0x910: a2 := 0, a3 := s7, a1 := s7. *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 2324.
{ sc_awr. }
sc_md.
sc_km HF KM. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG : forall n, (n < 512)%nat -> ew Ex n = ew (sc_E regs) n)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
  assert (HAE : env_agree 32 (Ereg regs []) Ex)
    by (split; [intros nn Hnn; try rewrite (AG nn) by lia; unfold sc_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs []
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] HS HAE
    ltac:(vm_compute; reflexivity)) as KR
end.
sc_reg_at HS (12%bv : bv 5) (w64 0) Q12 ltac:(reflexivity).
sc_reg_at HS (11%bv : bv 5) (w64 (upb + 0)) Q11
  ltac:(cbn [sv_denot]; try rewrite (AG 23%nat) by lia; rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
sc_reg_at HS (13%bv : bv 5) (w64 (upb + 0)) Q13
  ltac:(cbn [sv_denot]; try rewrite (AG 23%nat) by lia; rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
destruct Hfr as (F19 & F21 & F27).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H W) ?msx) =>
  assert (Hpt : forall x, ms_mem msx x = mem x) by exact KM;
  assert (Hinv : sc_inv B cx ly' S' W res upb 0 (ms_regs msx) (ms_mem msx) mdv);
  [ split; [apply (sc_core_pt B cx ly' S' W regs mem md (ms_regs msx) (ms_mem msx) mdv dec_ev_86c Hcore HJ Hpt);
            apply KR; sc_kin|];
    split; [split; [sc_keep KR|]; split; sc_keep KR|];
    split; [sc_keep KR|]; split; [sc_keep KR|]; split; [sc_keep KR|]; split; [sc_keep KR|];
    split; [rewrite Z.sub_0_r; sc_keep KR|];
    split; [exact Q11|]; split; [exact Q13|]; split; [exact Q12|];
    split; [intros j Hj; rewrite (sc_aview_pt _ _ _ Hpt); exact (Hfill j Hj)|];
    exact (sc_fsh_pt cx _ _ 0 4 (sc_aview_pt _ _ _ Hpt) Hfsh)
  | ] end.
pmkst HS. rewrite (sc_pc (rc := rc)).
apply (sc_loop (fx := fx') B LAWS cx W ly' S' res upb (ex_st_98c B MT cx) Hperm) with (m := Z.to_nat (ex_uolen cx)) (i := 0);
  [| rewrite Z2Nat.id by lia; lia | lia | exact Hinv].
(* +0x98c: ex_st_98c, with the events and the meter of +0x908. *)
intros regs2 mem2 md2 Hcore2 Hfr2 Q20 Q23 Hfsh2.
assert (Hcrt : 0 <= dec_crt_cost_max MT).
{ unfold dec_crt_cost_max.
  pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
pose proof (mo_free_nonneg MT MTL) as Hfree.
unfold ex_st_98c.
exists fx', ly', S', regs2, mem2, md2, dec_ev_86c, res, upb.
split; [reflexivity|]. split; [exact Hfrm|]. split; [exact Hcore2|].
split; [unfold dec_ev_86c, DEC_CRT_EV; lia|]. split; [exact Hperm|]. split; [exact Hres|]. split; [exact Hupb|].
split; [apply (mo_le_mono MT MTL _ _ _ _ Hmle); lia|].
split; [apply (mo_ok_le MT MTL _ _ _ Hmok); unfold dec_rest_86c; lia|].
split; [exact Hfr2|]. split; [exact Q20|]. split; [exact Q23 | exact Hfsh2].
Qed.
End sg.
