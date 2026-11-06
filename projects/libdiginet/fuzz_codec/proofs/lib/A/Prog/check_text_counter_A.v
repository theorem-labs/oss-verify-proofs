(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths and numbers changed; 1325 of its 1383 lines of code are new or changed and 335 lines of the source are left out. *)
(* check_text_counter (fuzz_codec.c:468-490) at image A 0x83b5c, 167 instructions, real frame 160 with sp realigned
   to 32 at 0x83b9c and a side-stack frame of class 0 requested at 0x83bd0, against lib/A/Prog/CPgChkC.v's
   cdc_check_text_counter_specX. a0 = q (the text), a1 = sg (the 24-byte array of the record), a2 = dt (the dots
   byte).

   The walk (the cuts and the last segment are in check_text_counter_A_inv.v and check_text_counter_A_E.v):
   - 0x83b5c-0x83bd0 the prologue (the 160-byte frame, the twelve saves, sp realigned to 32 in s1 = SP1), the two
     .got loads (the shadow offset SB, the use-after-return cell, whose value 1 decides the test at 0x83bc8),
     a0 = 64, jal 0x3d0fc.
   - the class-0 side-stack frame request (CPgWalkFrame.cpg_stack_malloc_keep): F in a0, its 8 shadow bytes zero,
     the flag address FL at F + 56.
   - 0x83bd4-0x83c6c the frame header (0x41B58AB3, the frame description, the function's own address), the eight
     shadow bytes f1 x4 | 00 | f3 x3 (the 8-byte buffer at F + 32 is the one variable), F at SP1 + 40, F + 32 at
     SP1 + 24, the want dots byte SP1 + 55 := 0.
   - 0x83c70 owed_counter_text(q, F + 32, SP1 + 55) through its contract.
   - 0x83c74-0x83c88 s7 = its rc, the memset of the record's 24 bytes to 0xa5 (aj_intrin_atS, OSet), the checked
     store dots := 0xa5 (0x83c8c-0x83c9c).
   - 0x83cac diginet_counter_text(q, sg, dt) through its contract; 0x83cb0 bne a0,s7 and, when both are 0, the bcmp
     wrapper on sg and F + 32 over 8 bytes (0x83cc4) and the checked compare of dt with SP1 + 55: the three aborts
     at 0x83dd0 are refuted by the agreement premise.
   - at 0x83ce0 the walk is the cut C5 of check_text_counter_A_inv.v, and check_text_counter_A_E.v's
     seg_ctc_E_holds ends it (the loop over sg[8..24), the release of the frame, cdc_post). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgSat CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
check_text_counter_A_inv check_text_counter_A_lib check_text_counter_A_E.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_OWED_CT : Z := 0x83df8.
Definition A_COUNTER_TEXT : Z := 0x86120.
Definition A_MEMSET : Z := 0x51e34.
Definition A_BCMP : Z := 0x422e0.
(* the use-after-return cell's .got slot and the cell: the prologue reads them *)
Definition ctc_rs0 : smem := [uar_got_region; uar_cell_region].

Lemma ctc_U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma ctc_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma ctc_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* lia over the arithmetic facts only: the walk's big hypotheses (the symbolic state, the journals, the memory facts)
   are cleared first, so that lia's preprocessing does not traverse them *)
Ltac ctc_clear_big :=
  repeat match goal with
  | H : ?T |- _ =>
    lazymatch type of T with Prop =>
    lazymatch T with
    | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail
    | cw_hold _ => fail | @eq nat _ _ => fail | le _ _ => fail | lt _ _ => fail
    | _ => clear H
    end end
  end.
Ltac ctc_lia := ctc_clear_big; lia.

(* A region of the walk kept across a call or a runtime call whose post gives KT2 (its tcj_kept): a stack region
   (the save area at atom 2, the spill slots at atom 33) above the callee's window and off its write set; the four
   image cells by their values in the journals before and after (val_mem facts in context). *)
Ltac ctc_kept KT2 :=
idtac; first
[ lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
  lazymatch goal with U : bv_unsigned (ew E n) = _ |- _ =>
  eapply (region_kept_tcj_stack _);
  [ exact KT2 | exact U
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha;
    split; [ctc_lia | split; [ctc_lia | first [solve [intros []] | let Hx := fresh in intros [Hx|Hx]; ctc_lia | let Hx := fresh in intros Hx; ctc_lia]]]
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; split; ctc_lia ] end end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  first
  [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [eassumption | eassumption | lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [eassumption | eassumption | lia]
  | change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [eassumption | eassumption | lia]
  | change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [eassumption | eassumption | lia] ] end ].

(* the two image cells of the use-after-return check, by their values in the journals J1 / J2 *)
Ltac ctc_uar J1 J2 :=
lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
let Kc2 := fresh "Kc" in let Ku2 := fresh "Ku" in let Kg2 := fresh "Kg" in let Kgu2 := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 J1)) as (Kc & Ku & Kg & Kgu);
destruct (al_const _ _ L _ _ _ _ _ (proj1 J2)) as (Kc2 & Ku2 & Kg2 & Kgu2);
rewrite (tl_got_uar _ TL), (tl_uar_cell _ TL) in Kgu, Kgu2; rewrite (tl_uar_cell _ TL) in Ku, Ku2;
first
[ change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob);
  [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgu) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgu2) | lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1);
  [exact (val_mem_of_rd32 tfibsegs _ _ _ _ Ku) | exact (val_mem_of_rd32 tfibsegs _ _ _ _ Ku2) | lia] ] end.
(* a region inside the walk's own frame (atom 38) or its shadow (atom 61), kept across a call whose post journal is J2
   by the callee's tcj_kept K: HJe the walk's entry journal, HFd the call state's frames, HFA the frame's address
   in the call state's layout *)
Ltac ctc_kept_fr K J2 HJe HFd HFA HFAd :=
lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
lazymatch goal with U : bv_unsigned (ew E n) = _ |- _ =>
lazymatch type of J2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ ?S3 _ _ _ _ =>
lazymatch type of HFd with frames ?Sd = _ =>
lazymatch goal with Hf3 : frames S3 = frames Sd |- _ =>
let L := rnLAWS in
let P := fresh "P" in let Pf := fresh "Pf" in let Ps := fresh "Ps" in
pose proof (ctc_frame_present_j _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe J2 (eq_trans Hf3 HFd) HFA) as P;
destruct P as (Pf & Ps);
eapply (region_kept_tcj_frame _);
[ exact K | exact U | rewrite HFd; left; reflexivity
| cbn [YP09.r_lo YP09.r_hi]; rewrite HFAd; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
  first [left; split; lia | right; split; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha;
  first [solve [intros []] | solve [match goal with NF : forall x, _ -> ~ _ |- _ => apply NF; lia end]
        | let Hx := fresh in intros [Hx|Hx]; lia | let Hx := fresh in intros Hx; lia]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  first [apply Pf; lia | apply Ps; lia] ] end end end end end.
Ltac ctc_kept_c K J1 J2 HJe HFd HFA HFAd :=
first [ ctc_kept K | cpw_kept_std K J1 J2 | ctc_uar J1 J2 | ctc_kept_fr K J2 HJe HFd HFA HFAd ].

(* lia, unhiding one hidden disjunction at a time *)
Ltac ctc_wlia := ctc_clear_big; first [ lia
  | match goal with H : cw_hold _ |- _ => let H' := fresh in pose proof H as H'; unfold cw_hold in H'; lia end ].
(* a run whose frame is HFr1 keeps the bytes of P: HK (forall a, P a -> aview .. m1 a = R a) moved to the run's end *)
Ltac ctc_kp P HK :=
lazymatch goal with
| HFr1 : frame_of ?Ev ?rs (mrestrict (w_H ?Wx) ?m1) (mrestrict _ ?m2) |- _ =>
  lazymatch type of HK with forall a, _ -> aview _ _ m1 a = @?R a =>
  let KP := fresh "KP" in let HK1 := fresh "HK" in
  pose proof (cw_kept_run (fun a => ~ P a) Ev rs (w_H Wx) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1
    ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
          intros a (r & Hr & Hb); cbv beta;
          lazymatch type of Hr with In _ ?rs0 => let rs' := eval vm_compute in rs0 in change (In r rs') in Hr end;
          unfold P;
          repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
            repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U in Hb end; ctc_wlia |]); destruct Hr)) as KP;
  assert (HK1 : forall a, P a -> aview tfibsegs (w_H Wx) m2 a = R a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; transitivity (aview tfibsegs (w_H Wx) m1 a);
        [apply KP; [unfold P in Ha; cbv beta in Ha; ctc_lia | let Hn := fresh in intros Hn; exact (Hn Ha)] | exact (HK a Ha)]);
  clear KP HK; rename HK1 into HK end end.

(* a run whose state has no write window: what the call kept and the byte facts HK (each with its bound HB) moved
   to the run's end *)
Ltac ctc_closed_fold :=
lazymatch goal with
| HFr1 : frame_of ?Ev ?rs (mrestrict (w_H ?Wx) ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
  let EQ := fresh "EQ" in
  pose proof (ctc_frame_of_closed Ev rs (w_H Wx) m1 m2
    ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
          intros a (r & Hr & Hb);
          lazymatch type of Hr with In _ ?rs0 => let rs' := eval vm_compute in rs0 in change (In r rs') in Hr end;
          repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
            first [clear - Hb; lia | ctc_lia] |]); destruct Hr) HFr1) as EQ;
  lazymatch goal with KT : tcj_kept tfibsegs ?Bv ?T ?lyc ?Sc ?W ?m0 Wx m1 ?sp ?Er, LW : AR_laws tfibsegs ?Bv,
    HARe : AR tfibsegs ?Bv ?lyc ?Sc ?W ?m0 ?mdc |- _ =>
    let KT2 := fresh "KT" in
    pose proof (cw_kept_step Bv LW T lyc Sc W m0 mdc Wx m1 m2 sp Er (fun _ => False) ltac:(lia) HARe KT
      (fun a Ha _ => EQ a Ha) (fun a (H : False) => match H with end) (fun a Hp => apresent_grows _ _ _ a HG1 Hp)) as KT2;
    clear KT; rename KT2 into KT end;
  repeat match goal with HK : forall a, ?P a -> aview _ (w_H Wx) m1 a = @?R a, HB : forall a, ?P a -> 0 <= a < 2 ^ 64 |- _ =>
    let HK1 := fresh "HK" in
    assert (HK1 : forall a, P a -> aview tfibsegs (w_H Wx) m2 a = R a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite (EQ a (HB a Ha)); exact (HK a Ha));
    clear HK; rename HK1 into HK end;
  clear EQ HFr1 HG1 end.

(* a save slot of the region RG (base atom 2 = the entry sp) holding the entry value of register r (atom j) *)
Ltac ctc_sv RG B2c HAEc j r od :=
  try unfold raZ;
  eapply (ctc_chunk8 _ _ 2 _ _ _ _ _ _ od j _ _ RG B2c ltac:(cbn [In]; repeat (first [left; reflexivity | right])));
  [ rewrite (proj1 HAEc j ltac:(lia)), (cw_ew_reg _ _ j r eq_refl); symmetry; apply Z_to_bv_bv_unsigned
  | lazymatch goal with |- 0 <= bv_unsigned ?x < _ =>
      let Hq := fresh in pose proof (bv_unsigned_in_range 64 x) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq end
  | lia ].

(* env_agree_chain, also through the token engine's extK *)
Ltac ctc_agree HAE :=
first [ exact HAE
| apply env_agree_havoc_ge; [cbv; lia | ctc_agree HAE]
| eapply env_agree_trans; [ | eapply env_agree_le; [ | apply env_agree_ewset ]; cbv; lia ]; ctc_agree HAE
| eapply env_agree_trans; [ | eapply env_agree_le; [ | apply env_agree_extK ]; cbv; lia ]; ctc_agree HAE ].

(* the region of HS with base atom b and low offset lo, as H *)
Ltac ctc_find_reg HS b lo H :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rec go l n := lazymatch l with
    | (YP09.mkRegion (Some b) lo _ _ _ _) :: _ => pose proof (st_ok_region_nth Ev ssx msx n _ HS eq_refl) as H
    | _ :: ?t => go t constr:(S n) end in go rs 0%nat end.

(* keep lia from case-splitting: hide the disjunctions and the implications from an equation *)
Ltac ctc_hide := repeat match goal with
  | H : _ \/ _ |- _ => cw_hide H
  | H : _ /\ (_ \/ _) |- _ => cw_hide H
  | H : ?A -> _ |- _ => lazymatch type of A with Prop => lazymatch A with _ = _ => cw_hide H end end
  end.

(* the awr_ok of a state that holds the walk's own frame (atom 38), its shadow (61), the realigned sp (33) and the
   entry sp (2) *)
Ltac ctc_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; ctc_lia|]
| match goal with
  | HU : bv_unsigned (ew _ 38) = _, HO : In (0, _) _ |- _ =>
    eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 _ 38%nat);
    [reflexivity | exact HU | exact HO | cbn [YP09.r_wlo]; ctc_lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 0) with 64; ctc_lia |] end
| match goal with
  | HU : bv_unsigned (ew _ 61) = _, HO : In (0, _) _ |- _ =>
    eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 _ 61%nat);
    [reflexivity | exact HU | exact HO | cbn [YP09.r_wlo]; ctc_lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 0 / 8) with 8; ctc_lia |] end
| match goal with
  | HU : bv_unsigned (ew _ ?n) = ?b, HW : forall a, ?b <= a < ?b + 1 -> awr_byte _ _ _ _ _ _ _ a |- _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n b);
    [reflexivity | exact HU | cbn [YP09.r_wlo YP09.r_whi]; let x := fresh in let Hx := fresh in intros x Hx; apply HW; ctc_lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 33) = ?v |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (v - s0));
    [reflexivity | rewrite HU; ctc_lia | cbn [YP09.r_wlo YP09.r_whi]; ctc_lia
    | cbn [YP09.r_wlo YP09.r_whi]; ctc_lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 2) = ?v |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (v - s0));
    [reflexivity | rewrite HU; ctc_lia | cbn [YP09.r_wlo YP09.r_whi]; ctc_lia
    | cbn [YP09.r_wlo YP09.r_whi]; ctc_lia |] end ].
(* the write windows of such a state lie in the zone the goal names *)
Ltac ctc_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ctc_lia |]); destruct Hr.

Variables SEG7TBL GLYPHA PERSA : Z.
Variable ROSTRS : list (Z * Z).

(* At 0x83ce0 the walk is the cut C5 of check_text_counter_A_inv.v; check_text_counter_A_E.v ends it. *)
Lemma ctc_c5_done : astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
  forall g pos (W2 : world tfibsegs) ly2 S2 regs2 mem2 md2,
  ctc_pre B SEG7TBL GLYPHA ROSTRS g ->
  ajournal tfibsegs B (x_STK g) (x_sp0 g) (x_FP g) (x_ly g) (x_S g) (x_W0 g) (x_mem0 g) (x_md0 g)
    ((0, pos) :: x_own g) ly2 S2 W2 mem2 md2 (x_k g) ->
  tcj_kept tfibsegs B T_check_text_counter (x_lyc g) (x_Sc g) (x_W g) (x_memc g) W2 mem2 (x_sp g) (ctc_E g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (x_lyc g) (x_Sc g)) -> ~ In (0, pos) (frames (x_Sc g)) ->
  mo_le MT (x_Sc g) S2 0 -> same_io (x_mdc g) md2 ->
  ctc_common g pos W2 regs2 mem2 -> ctc_P5 g ly2 S2 W2 regs2 mem2 md2 ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 CTC_C5) mem2 (seg_rom tfibsegs)) md2) (ctc_post B MT g).
Proof.
intros ASF FFL g pos W2 ly2 S2 regs2 mem2 md2 Hpre HJ HK Hp Hn Hm Hi Hc HP.
eapply (seg_ctc_E_holds B MT); try eassumption.
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|]. split; [exact Hp|]. split; [exact Hn|].
split; [exact Hm|]. split; [exact Hi|]. split; [exact Hc | exact HP].
Qed.

(* The callee contracts (owed_counter_text at 0x83df8, diginet_counter_text at 0x86120), then the runtime contracts
   the walk reaches: the class-0 side-stack frame request with its progress law, the frame release and flag laws, the
   memset intrinsic, the bcmp wrapper. *)
Theorem check_text_counter_A_holds :
cdc_owed_counter_text_specX tfibsegs B MT CA_RLO CA_RHI GLYPHA ROSTRS A_OWED_CT ->
cdc_counter_text_specX tfibsegs B MT CA_RLO CA_RHI SEG7TBL A_COUNTER_TEXT ->
astack_malloc_realizes tfibsegs B 0 -> stack_malloc_progressP B ->
astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
aintrin_realizes tfibsegs B OSet A_MEMSET -> abcmp_realizes tfibsegs B A_BCMP ->
cdc_check_text_counter_specX tfibsegs B MT CA_RLO CA_RHI SEG7TBL GLYPHA ROSTRS CTC_A.
Proof using MTL MTF TL LAWS ML.
intros OCT CTX ASM0 SMP ASF FFL AMS ABC.
unfold cdc_check_text_counter_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj
  HE H10 Hstr Hoq Hosg Hodt H11 Hdst Hsj Hsjl H12 Hddst Hdv Hd1 Hd2 Hd3 Himg Hagr Hfr.
assert (Hpre : ctc_pre B SEG7TBL GLYPHA ROSTRS (mkCtc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj))
  by exact (conj HE (conj H10 (conj Hstr (conj Hoq (conj Hosg (conj Hodt (conj H11 (conj Hdst (conj Hsj (conj Hsjl
    (conj H12 (conj Hddst (conj Hdv (conj Hd1 (conj Hd2 (conj Hd3 (conj Himg (conj Hagr Hfr)))))))))))))))))).
(* the entry journal stays as HJ0; the runs take the newest journal, HJ *)
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as HJ1. rename HJ into HJ0. rename HJ1 into HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_counter HE
  ltac:(unfold T_check_text_counter, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_counter, ESTACK in *.
assert (HS : st_ok tfibsegs (Ereg regs (cw_extra []))
  (mkSS CTC_A sr_atoms (cw_regs 160 ++ ctc_rs0) None (mkFacts cw_atoms [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 CTC_A) memc (seg_rom tfibsegs)))).
{ apply (cw_entry B TL LAWS CTC_A 160 [] ctc_rs0 [] lyc Sc W regs memc mdc HAR ltac:(lia)).
  - lia.
  - exact Hal.
  - intros a Ha. apply Hpres. lia.
  - vm_compute. reflexivity.
  - destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (_ & Kuar & _ & Kguar).
    rewrite (tl_got_uar B TL), (tl_uar_cell B TL) in Kguar. rewrite (tl_uar_cell B TL) in Kuar.
    unfold ctc_rs0, uar_got_region, uar_cell_region. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_GOT_uar 8 (SLit A_uar_glob) A_uar_glob);
      [reflexivity | unfold A_uar_glob; zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ 0 A_uar_glob 4 (SLit 1) 1);
      [reflexivity | zside | zside |].
      rewrite Z.add_0_l. exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar).
  - unfold cw_regs, stack_region, got_region, bcell_region, ctc_rs0, uar_got_region, uar_cell_region.
    cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl).
    change (bv_unsigned (getr regs 2)) with (spZ regs).
    unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob. repeat split; lia.
  - exact I. }
remember (Ereg regs (cw_extra [])) as E0 eqn:HE0 in HS.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E0) by (rewrite HE0; apply env_agree_refl).
assert (E1 : ew E0 1 = getr regs 1) by (rewrite HE0; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite HE0, (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (E2 : ew E0 2 = getr regs 2) by (rewrite HE0; exact (cw_ew_reg regs _ 2 2%bv eq_refl)).
assert (E3 : ew E0 3 = getr regs 3) by (rewrite HE0; exact (cw_ew_reg regs _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (rewrite HE0; exact (cw_ew_reg regs _ 4 4%bv eq_refl)).
assert (E10 : ew E0 10 = Z_to_bv 64 q) by (rewrite HE0, (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E0 11 = Z_to_bv 64 sg) by (rewrite HE0, (cw_ew_reg regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E0 12 = Z_to_bv 64 dt) by (rewrite HE0, (cw_ew_reg regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite HE0; apply cw_ew_SB).
clear HE0.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 8384
  (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1) HJ0 ltac:(lia) ltac:(lia)) as KT.
assert (HFRS : frames Sc = frames Sc) by reflexivity.
assert (HPERM : Permutation (ablocks B lyc Sc) (ablocks B lyc Sc)) by apply Permutation_refl.
assert (HIO : same_io mdc mdc) by apply same_io_refl.
assert (HMO : mo_le MT Sc Sc 0) by (apply mo_le_refl; exact MTL).
unfold cfg_at. change (w64 CTC_A) with (Z_to_bv 64 CTC_A).
(* 0x83b5c-0x83bcc: the prologue, the two .got loads, the cell's 1 decides the test, a0 = 64, jal 0x3d0fc *)
cw_run cw_awr_stk. cpw_keep cw_kwr_stk.
set (SP1 := 32 * ((spZ regs + -160) / 32)).
destruct (sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold SP1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= SP1 <= spZ regs - 160) by lia. clear Hsp1r.
assert (HSP1e : ctc_sp1 (spZ regs) = SP1) by reflexivity.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 SP1)
(ctc_denot_and_m32 Ev 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 SP1)
(eq_trans (U_inj Ev _ _ (ctc_U_add0 Ev _))
(ctc_denot_and_m32 Ev 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia))) R9 end.
(* sp = s1 = SP1: the fresh atom 33 *)
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 33 Ev (havoc Ev 33 [Z_to_bv 64 SP1]) ssv msv HS
(env_agree_havoc_ge 33 33 Ev Ev _ ltac:(lia) (env_agree_refl 33 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
assert (E33 : ew (havoc Ev 33 [Z_to_bv 64 SP1]) 33 = Z_to_bv 64 SP1)
  by exact (ew_havoc_new _ 33 [Z_to_bv 64 SP1] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
clear HS. rename HS3 into HS. cpw_rebase.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (U33 : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 33 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, R2; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (9%bv : bv 5) (SOff 33 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact R9)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* the fact of SP1, the save area trimmed to [sp - 104, sp), the spill slots 24(s1), 40(s1) and the want dots
   byte 55(s1) *)
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 33 (mkAF (2 ^ 46 - 256) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS
  ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk1 & _).
pose proof Hstk1 as (Hsp0al & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 33%nat) 24 48 24 48 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U33; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply Hpres1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U33, B2; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 33%nat) 55 56 55 56 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U33; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply Hpres1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U33, B2; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* 0x83bd0 jal 0x3d0fc: the class-0 side-stack frame request *)
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
pose proof (ctc_count_le 0 (frames Sc)) as Hcnt.
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
replace 250108 with (pc_stack_malloc (as_code B) 0) by (rewrite (tl_code B TL); reflexivity);
eapply SRr_bind;
[ eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS tfib_segs_low (tl_env B TL) ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (SP1 - sp0) (Z_to_bv 64 539604) HJ)
| ] end.
- unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite R3, E3. exact Hgp.
- rewrite R4, E4. exact Htp.
- exact R1.
- apply ret_ok_even. vm_compute. reflexivity.
- change (fs_frames 0) with 16384. lia.
- cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin
    & Hnev2 & Hbb2 & Hz & Hflag & HK & HSf & HKown & HSio).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  replace (sp0 + (SP1 - sp0)) with SP1 in HK, HKown by lia.
  assert (HKA : tcj_kept tfibsegs B ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (fun _ => False)).
  { eapply (cw_tcj_of_acall B ESTACK lyc Sc W (ms_mem ms) W mem2 SP1 (SP1 - ESTACK) SP1 (fun _ => False));
    [lia | lia | exact HK | intros a Ha; apply Hpres2; unfold ESTACK in *; lia]. }
  pose proof (cw_kept_call B 8384 lyc Sc W memc W (ms_mem ms) mem2 (spZ regs) (SP1 - ESTACK) SP1
    (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(lia) KT HK) as KT2.
  clear KT. rename KT2 into KT.
  aconstsF HJ Kgot1 Kcell1 Kguar1 Kuar1. aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
  let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
  let HS2 := fresh "HS2" in
  jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q); [cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; ctc_kept HKA
    | specialize (HS2 HQ); clear HQ] end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  let j := eval vm_compute in (K + 4)%nat in
  lazymatch type of HS with st_ok _ (havoc ?E0 ?K0 ?ws0) _ _ =>
  assert (HA0 : ew (havoc E0 K0 ws0) j = getr regs2 10)
    by exact (ew_havoc_new E0 K0 ws0 4 (Z_to_bv 64 0) ltac:(cbn [length map CLOB]; lia)) end end.
  cpw_rebase.
  (* the frame F (atom 38, a0), its flag address FL (60) and its shadow base (61) *)
  assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds tfibsegs B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
  destruct (frame_al64 tfibsegs B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
  pose proof (frm_off_img B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as HFimg.
  destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
  change (fs_frame_bytes 0) with 64 in *.
  set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
  pose proof HFimg as HFimg'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg'.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite (Z.div_mod F 64) at 1 by lia; rewrite HF64, Z.add_0_r;
        replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (HF8a : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HF8b : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia).
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E38 : ew Ev 38 = Z_to_bv 64 F) by (rewrite HA0, Ha0; reflexivity) end.
  clear HA0.
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_agree tfibsegs 60 Ev (havoc Ev 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) ssv msv HS
  (env_agree_havoc_ge 60 60 Ev Ev _ ltac:(lia) (env_agree_refl 60 Ev)) ltac:(vm_compute; reflexivity)) as HS3;
  assert (E60 : ew (havoc Ev 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) 60 = Z_to_bv 64 FL)
    by exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 0 (Z_to_bv 64 0) ltac:(cbn; lia));
  assert (E61 : ew (havoc Ev 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)]) 61 = Z_to_bv 64 (shadow_addr F))
    by (change 61%nat with (60 + 1)%nat;
        exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (shadow_addr F)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
  clear HS. rename HS3 into HS. cpw_rebase.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  destruct (cw_frame_afacts B LAWS Ev 38 60 61 lyc S2 W mem2 md2 0 fpos FFL HAR2 Hfin2 E38 E60 E61) as (AF38 & AF60 & AF61) end.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev _ msx 61 _ (st_ok_add_fact tfibsegs Ev _ msx 60 _
    (st_ok_add_fact tfibsegs Ev ssx msx 38 _ HS AF38) AF60) AF61) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U38 : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U60 : bv_unsigned (ew Ev 60) = FL) by (rewrite E60; apply unsigned_lit_small; lia);
  assert (U61 : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
  destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFal32 & _ & HFpres & HFSpres).
  change (fs_frame_bytes 0) with 64 in HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
  fold F in HFpres, HFSpres. fold FL in HFLown.
  assert (HFno : forall a, F <= a < F + 64 -> ~ aowned B lyc S2 a)
    by (intros a Ha; exact (proj2 (HFpres a Ha))).
  assert (HFSno : forall a, shadow_addr F <= a < shadow_addr F + 8 -> ~ aowned B lyc S2 a).
  { intros a Ha. pose proof (HFSpres (a - shadow_addr F) ltac:(lia)) as Hx.
    replace (shadow_addr F + (a - shadow_addr F)) with a in Hx by lia. exact (proj2 Hx). }
  assert (HFLF : FL + 1 <= F \/ F + 64 <= FL)
    by (destruct (cw_flag_apart B lyc S2 FL F (F + 64) HFLown HFno) as [Hx|Hx]; [right | left]; lia).
  assert (HFLS : FL + 1 <= shadow_addr F \/ shadow_addr F + 8 <= FL)
    by (destruct (cw_flag_apart B lyc S2 FL (shadow_addr F) (shadow_addr F + 8) HFLown HFSno) as [Hx|Hx];
        [right | left]; lia).
  assert (HFS : F + 64 <= shadow_addr F \/ shadow_addr F + 8 <= F).
  { unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
    destruct HFapp as (_ & [Hl | Hh]); [left | right]; lia. }
  assert (HSlo : SHADOW_OFF + 512 <= shadow_addr F) by (unfold shadow_addr; lia).
  assert (HShi : shadow_addr F + 8 <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr; lia).
  unfold SHADOW_OFF in HSlo, HShi.
  (* the frame in two parts around the 8-byte buffer at F + 32 (the owed callee writes it): [F, F + 32) and
     [F + 40, F + 64) with the flag address at F + 56; its 8 shadow bytes, zero after the request *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 38%nat) 0 32 0 32 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U38; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite U38, U33, B2; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
      repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 38%nat) 40 64 40 64 [YP09.mkChunk 56 (CVal 8 (SOff 60 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U38; split; [lia|]; split; [lia|]; split;
      [ intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (HFpres (F + o) ltac:(lia)))
      | apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val tfibsegs Ev _ F 56 8 (SOff 60 0) FL);
        [ cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia
        | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag) ] ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite U38, U33, B2; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
      repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (cw_fshadow_region 61 0) HS eq_refl
    (cw_fshadow_region_ok B LAWS Ev 61 lyc S2 W mem2 md2 0 fpos HAR2 Hfin2 E61 Hz)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, cw_fshadow_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
      rewrite U61, U38, U33, B2; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
      repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  (* the shadow of a frame byte is the frame-shadow region's *)
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_alias tfibsegs Ev ssx msx _ _ HS (shadow_decl_ok Ev 38 32 61 F SB E38 ltac:(lia) E32 E61)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  (* 0x83bd4-0x83c6c: s2 = s9 = F (bnez taken), F at SP1 + 40, the frame header, the eight shadow bytes, the want
     dots byte, F + 32 at SP1 + 24; a0 = q, a1 = F + 32, a2 = SP1 + 55; jal owed_counter_text *)
  assert (HOWN : In (0, fpos) ((0, fpos) :: own)) by (left; reflexivity).
  aj_run_to_sh tfibtbl_lib_ok HS HJ2 A_OWED_CT.
  { ctc_awr. }
  cw_norm_model.
  (* what the call has kept of its entry state, carried through the request and the header *)
  assert (HZfr : forall a, (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL ->
    cw_fresh B lyc Sc a).
  { intros a Ha. apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
      lyc S2 W _ _ k 0 fpos a HJ0 HJ2 ltac:(rewrite Eab; apply Permutation_refl)).
    change (fs_frame_bytes 0) with 64. change (64 / 8) with 8.
    unfold frame_rng, in_zr. cbn [fst snd]. fold F FL. exact Ha. }
  lazymatch goal with
  | HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
    pose proof (cw_kept_run (fun a => (spZ regs - 8384 <= a < spZ regs) \/
        ((F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL))
      Ev rs (w_H W) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(ctc_kwr)) as KR;
    pose proof (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W m1 m2 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)
      (fun a => (spZ regs - 8384 <= a < spZ regs) \/
        ((F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL))
      ltac:(ctc_lia) HAR KT KR
      ltac:(intros a [Ha | Ha]; [left; exact Ha | right; right; exact (HZfr a Ha)])
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    clear KT KR HFr1 HG1; rename KT2 into KT end.
  (* the chain from the call state to the walk's state: the request's frame in front, the blocks, the input, the
     meter *)
  clear HFRS HPERM HIO HMO.
  rename Hfrs2 into HFRS.
  destruct (cw_frame_start MT MTL MTF B lyc Sc S2 HSf) as (HPERM & HMO).
  assert (HIO : same_io mdc md2)
    by (eapply same_io_trans; [apply cw_same_io_wvb | exact HSio]).
  (* ---- 0x83c70 owed_counter_text(q, F + 32, SP1 + 55) through its contract ---- *)
  assert (HFA0 : frame_addr lyc 0 fpos = F) by reflexivity.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
  pose proof HJ2 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  rreg HS (2%bv : bv 5) Q2. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11. rreg HS (12%bv : bv 5) Q12.
  assert (Usp : spZ (ms_regs msA) = SP1) by (unfold spZ; rewrite Q2; exact U33).
  assert (A10 : getr (ms_regs msA) 10 = w64 q) by (rewrite Q10; exact E10).
  assert (A11 : getr (ms_regs msA) 11 = w64 (F + 32)) by (rewrite Q11, U38; reflexivity).
  assert (A12 : getr (ms_regs msA) 12 = w64 (SP1 + 55)) by (rewrite Q12, U33; reflexivity).
  clear Q2 Q10 Q11 Q12.
  assert (HappE : forall x, (sg <= x < sg + 24 \/ dt <= x < dt + 1) -> amem_range x 1).
  { pose proof Hdst as (_ & _ & _ & _ & _ & _ & Hsam & _). pose proof Hddst as (_ & _ & _ & _ & _ & _ & Hdam & _).
    intros x [Hx|Hx]; unfold amem_range in *; lia. }
  assert (Hbl3 : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc S2))
    by (intros b m Hb; rewrite Eab; exact Hb).
  assert (Hfr3 : incl (frames Sc) (frames S2)) by (rewrite HFRS; apply incl_tl, incl_refl).
  assert (Hqtb : forall x, q <= x < q + Z.of_nat (length tb) -> ~ (sg <= x < sg + 24 \/ dt <= x < dt + 1))
    by (intros x Hx Hy; clear - Hx Hy Hd2 Hd3; lia).
  pose proof Hstr as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & Hqcw)).
  assert (Astr : cstr_rd tfibsegs W (ms_mem msA) (spZ (ms_regs msA)) T_owed_counter_text q tb).
  { rewrite Usp. eapply (ctc_cstr_up B LAWS) with (HAR := HAR) (HAR2 := HAR3) (Hbl := Hbl3) (Hfr := Hfr3)
      (Hfa := fun c p => eq_refl) (KT := KT) (Happ := HappE); [exact Hstr | exact Hoq | exact Hqtb |].
    unfold coff_win, T_owed_counter_text, ESTACK in *. lia. }
  assert (Aoq : cobj_ok B lyc S2 q (Z.of_nat (length tb)))
    by (eapply (ctc_cobj_up B) with (Hbl := Hbl3) (Hfr := Hfr3) (Hfa := fun c p => eq_refl); exact Hoq).
  assert (Aosg : cobj_ok B lyc S2 (F + 32) 8) by (apply (sat_c0_cobj B lyc S2 fpos F 32 8 Hfin2 eq_refl); lia).
  (* the frame's shadow byte of F + 32 is 0 (the region of atom 61, chunk 4) *)
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_region_nth Ev ssx msx 0 _ HS eq_refl) as RG0 end.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 4 1 (SLit 0) RG0 U61 ltac:(cbn; tauto) ltac:(lia)) as V4.
  cbn [sv_denot N.to_nat Pos.to_nat] in V4. rewrite unsigned_lit_small in V4 by lia. change (0 mod 2 ^ (8 * Z.of_N 1)) with 0 in V4.
  assert (AV4 : aview tfibsegs (w_H W) (ms_mem msA) (shadow_addr F + 4) = Some 0)
    by (exact (aview_of_val_mem1 tfibsegs _ _ _ _ V4 ltac:(lia))).
  clear RG0 V4.
  assert (ABS : block_shadow (aview tfibsegs (w_H W) (ms_mem msA)) SHADOW_OFF (F + 32) 8).
  { split; [rewrite Z.add_mod, (mod64_mod8 F HF64) by lia; reflexivity|]. split; [lia|].
    intros i Hi. change ((8 + 7) / 8) with 1 in Hi. assert (i = 0) by lia. subst i.
    replace (shadow_of_addr SHADOW_OFF (F + 32) + 0) with (shadow_addr F + 4)
      by (unfold shadow_of_addr, shadow_addr; rewrite (div8_of_mod8 F 32 (mod64_mod8 F HF64)); change (32 / 8) with 4; lia).
    exact AV4. }
  assert (Adst : cdst_ok tfibsegs B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W (ms_mem msA) (spZ (ms_regs msA))
    T_owed_counter_text (F + 32) 8).
  { rewrite Usp. apply (sat_c0_obj_dst tfibsegs B LAWS STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W (ms_mem msA) _ k SP1
      T_owed_counter_text fpos F 8 HJ2 HOWN Hfin2 eq_refl HF64 ltac:(lia) ltac:(lia) ABS);
    unfold T_owed_counter_text, ESTACK; lia. }
  destruct (garr8_of_present tfibsegs (mrestrict (w_H W) (ms_mem msA)) (F + 32) 8) as (sj0 & Asjl & Asj).
  { intros a Ha. destruct (al_frames _ _ LAWS lyc S2 W (ms_mem msA) _ 0 fpos HAR3 Hfin2) as (_ & _ & Hp & _).
    change (fs_frame_bytes 0) with 64 in Hp. destruct (Hp a ltac:(fold F; lia)) as ((Hh & b & Hb) & _).
    exists b. unfold mrestrict. rewrite Hh. exact Hb. }
  assert (Adt : (cdst_ok tfibsegs B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W (ms_mem msA) (spZ (ms_regs msA))
       T_owed_counter_text (SP1 + 55) 1 /\ cobj_ok B lyc S2 (SP1 + 55) 1) \/
    cdstk_ok tfibsegs B STK sp0 FP ly S lyc S2 ((0, fpos) :: own) W (ms_mem msA) (spZ (ms_regs msA))
       T_owed_counter_text (SP1 + 55) 1).
  { right. rewrite Usp. eapply (sat_stack_dst tfibsegs B LAWS STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W (ms_mem msA) _ k);
    [exact HJ2 | lia | lia | lia | lia | unfold T_owed_counter_text, ESTACK; lia]. }
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_region_nth Ev ssx msx 3 _ HS eq_refl) as RG3 end.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 55 1 (SLit 0) RG3 U33 ltac:(cbn; tauto) ltac:(lia)) as Adj.
  cbn [sv_denot N.to_nat Pos.to_nat] in Adj. rewrite unsigned_lit_small in Adj by lia. change (0 mod 2 ^ (8 * Z.of_N 1)) with 0 in Adj.
  clear RG3.
  assert (Ad1 : F + 32 + 8 <= SP1 + 55 \/ SP1 + 55 + 1 <= F + 32) by lia.
  destruct (ctc_obj_apart B LAWS lyc Sc lyc S2 W (ms_mem msA) _ fpos q (Z.of_nat (length tb)) HAR3 HFRS
    (fun c p => eq_refl) Hbl3 Hoq ltac:(lia)) as (Hqc & HqF).
  assert (Ad2 : q + Z.of_nat (length tb) <= F + 32 \/ F + 32 + 8 <= q) by (fold F in HqF; lia).
  assert (Ad3 : q + Z.of_nat (length tb) <= SP1 + 55 \/ SP1 + 55 + 1 <= q) by lia.
  assert (Aimg : cimg_rd tfibsegs B CA_RLO CA_RHI W (ms_mem msA) (spZ (ms_regs msA)) T_owed_counter_text
    ((GLYPHA, 464) :: ROSTRS)).
  { rewrite Usp. apply (ctc_cimg_up B lyc Sc W memc W (ms_mem msA) 8384 (spZ regs) _ KT _ _ _ _ _ _ Himg);
    [unfold T_owed_counter_text, ESTACK; lia | lia | intros r Hr; right; exact Hr]. }
  assert (Afr : Z.of_nat (length (frames S2)) <= 8) by (rewrite HFRS; cbn [length]; lia).
  ctc_hide.
  unfold cw_hold in HFS.
  rreg HS (1%bv : bv 5) Y1. rreg HS (2%bv : bv 5) Y2. rreg HS (3%bv : bv 5) Y3. rreg HS (4%bv : bv 5) Y4.
  assert (Esp : spZ (ms_regs msA) = SP1) by exact Usp.
  lazymatch type of HS with st_ok _ ?Ev ?ss _ => lazymatch goal with |- SRr _ _ (mkCfg _ ?mdd) _ =>
  eapply (cpw_call W Ev ss msA mdd) end end.
  { exact HS. }
  { reflexivity. }
  { eapply OCT.
    { eapply cpw_entry.
      - exact HJ2.
      - rewrite Y1; apply ret_ok_even; vm_compute; reflexivity.
      - unfold raZ; rewrite Y1, unsigned_lit_small by lia; lia.
      - rewrite Y3, (proj1 HAE 3%nat ltac:(lia)), (cw_ew_reg regs _ 3 3%bv eq_refl); assumption.
      - rewrite Y4, (proj1 HAE 4%nat ltac:(lia)), (cw_ew_reg regs _ 4 4%bv eq_refl); assumption.
      - rewrite Esp; first [rewrite Zminus_mod, Hal; reflexivity | assumption].
      - rewrite Esp; lazymatch goal with |- _ <= _ - ?T1 => let t := eval cbv in T1 in change T1 with t end; lia.
      - rewrite Esp; lia.
      - first [assumption | unfold EV_CDC in *; lia].
      - exact HPERM.
      - exact Hlive. }
    all: eassumption. }
  cbv beta; intros W3 c3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & HRc).
  rewrite Y1.
  rewrite Esp in KT3.
  lazymatch type of KT3 with tcj_kept _ _ ?T1 _ _ _ _ _ _ _ _ => let t := eval cbv in T1 in change T1 with t in KT3 end.
  lazymatch type of HS with st_ok _ _ ?ss _ => let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
  jafter_call_keep HS K regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 4; 5; 6; 7; 8; 9]%nat HS2 end.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; ctc_kept_c KT3 HJ2 HJ3 HJ0 HFRS HFA0 HFA0. }
  specialize (HS2 HQ). clear HQ.
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok _ (havoc ?E0 ?K0 ?ws0) _ _ =>
  assert (HA0c : ew (havoc E0 K0 ws0) 66 = getr regs3 10)
    by exact (ew_havoc_new E0 K0 ws0 4 (Z_to_bv 64 0) ltac:(cbn [length map CLOB]; lia)) end.
  cpw_rebase.
  assert (KTn : tcj_kept tfibsegs B 8384 lyc Sc W memc W3 mem3 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)).
  { eapply (cw_kept_cj B LAWS) with (1 := HJ0) (2 := HJ2) (4 := HPERM) (10 := KT) (11 := KT3).
    - first [apply incl_refl | rewrite HFRS; first [apply incl_refl | apply incl_tl, incl_refl]].
    - lia.
    - lia.
    - lia.
    - lia.
    - let a := fresh "a" in let Ha := fresh "Ha" in intros a [Ha | Ha];
          [right; right; apply HZfr; left; lia | left; lia]. }
  pose proof (eq_trans Hfrs3 HFRS) as HFRSn.
  pose proof (Permutation_trans HPerm3 HPERM) as HPERMn.
  assert (HIOn : same_io mdc md3) by (apply (fun H => same_io_trans _ _ _ H HIO3); cpw_io).
  pose proof (mle_station _ _ _ _ 0 0 MTL HMO HMLE3) as HMOn.
  rewrite Z.add_0_r in HMOn.
  lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (?k1 + EV_CDC) =>
    replace (k1 + EV_CDC) with k1 in HJ3 by (unfold EV_CDC; lia) end.
  clear Y1 Y2 Y3 Y4 Esp HP3 HIO3 Hfrs3 HPerm3 HMLE3 KT3 HFRS HPERM HIO HMO KT.
  rename KTn into KT. rename HFRSn into HFRS. rename HPERMn into HPERM. rename HIOn into HIO. rename HMOn into HMO.
  cw_norm_model.
  (* the owed result: rc in a0 (atom 66), the eight digits at F + 32 and the want dots byte when rc = 0 *)
  revert HRc Hagr. destruct (owed_counter_text_spec tb) as [[ro so] dob] eqn:HOW. intros HRc Hagr.
  revert Hagr. destruct (counter_text_spec tb) as [[rl sl] dl] eqn:HCT. intros Hagr.
  destruct Hagr as (Hrr & Hsd).
  destruct HRc as (HR10 & HR0 & HRn).
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E66 : ew Ev 66 = Z_to_bv 64 ro) by (rewrite HA0c, HR10; reflexivity) end.
  clear HA0c.
  assert (HWNT : exists sw v2, garr8 tfibsegs (mrestrict (w_H W3) mem3) (F + 32) sw /\ length sw = 8%nat /\
    val_mem tfibsegs (mrestrict (w_H W3) mem3) (SP1 + 55) 1 v2 /\ (ro = 0 -> sw = so /\ v2 = dob)).
  { destruct (Z.eq_dec ro 0) as [H0|H0].
    - destruct (HR0 H0) as (G & V). exists so, dob.
      split; [exact G|]. split; [exact (ctc_owed_len tb ro so dob HOW H0)|]. split; [exact V|].
      intros _. split; reflexivity.
    - destruct (HRn H0) as (sw & v2 & G & L & V). exists sw, v2.
      split; [exact G|]. split; [exact L|]. split; [exact V|]. intros Hc. contradiction. }
  destruct HWNT as (sw & v2 & Gsw & Lsw & Vv2 & Hwnt).
  clear HR0 HRn.
  (* the bytes the walk compares later, the owed digits at F + 32 and the want dots byte, kept from here on *)
  ctc_hide.
  set (PK := fun a => F + 32 <= a < F + 40 \/ a = SP1 + 55).
  assert (HKF : forall a, PK a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by reflexivity.
  (* the state after the call: the frame at the same address, the entry's blocks and frames *)
  destruct (ctc_frame_addr_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k _ ly3 S3 W3 mem3 md3 k HJ0 HJ3)
    as (Efa3 & Efl3).
  pose proof HJ3 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
  assert (Hbl4 : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly3 S3))
    by (intros b m Hb; exact (Permutation_in _ (Permutation_sym HPERM) Hb)).
  assert (Hfr4 : incl (frames Sc) (frames S3)) by (rewrite HFRS; apply incl_tl, incl_refl).
  pose proof Hdst as (_ & _ & Htsg & Htwsg & _ & _ & Hsgam & _).
  pose proof Hddst as (_ & _ & Htdt & Htwdt & _ & _ & Hdtam & _).
  destruct (ctc_dst_facts B LAWS FFL ly3 S3 W3 mem3 md3 lyc Sc fpos sg 24 HAR4 HFRS Hnin Efa3 Efl3 HPERM Htsg ltac:(lia))
    as (Hsgapp & Hsgimg & Hsgc & HsgF & HsgL & _).
  destruct (ctc_dst_facts B LAWS FFL ly3 S3 W3 mem3 md3 lyc Sc fpos dt 1 HAR4 HFRS Hnin Efa3 Efl3 HPERM Htdt ltac:(lia))
    as (Hdtapp & Hdtimg & Hdtc & HdtF & HdtL & _).
  fold F in HsgF, HdtF. fold FL in HsgL, HdtL.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hsgapp, Hdtapp.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hsgimg, Hdtimg.
  assert (Hsg4 : 4096 <= sg) by (destruct Hsgapp as (Q & _); exact Q).
  assert (Hdt4 : 4096 <= dt) by (destruct Hdtapp as (Q & _); exact Q).
  ctc_hide.
  pose proof Hdst as (Hsg0 & Hsg63 & _).
  pose proof Hddst as (Hdt0 & Hdt63 & _).
  (* ---- 0x83c74-0x83c88: s7 = rc, a0 = sg, a1 = 0xa5, a2 = 24; jal __asan_memset ---- *)
  assert (U38f : bv_unsigned (ew E0 38) = frame_addr ly3 0 fpos) by (rewrite Efa3; exact U38).
  assert (U61f : bv_unsigned (ew E0 61) = shadow_addr (frame_addr ly3 0 fpos)) by (rewrite Efa3; exact U61).
  aj_run_to_sh tfibtbl_lib_ok HS HJ3 A_MEMSET.
  { ctc_awr. }
  cw_norm_model.
  ctc_kp PK HKF.
  lazymatch goal with
  | HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
    pose proof (cw_kept_run (fun a => (spZ regs - 8384 <= a < spZ regs) \/
        ((F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL))
      Ev rs (w_H W3) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(ctc_kwr)) as KR;
    pose proof (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W3 m1 m2 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)
      (fun a => (spZ regs - 8384 <= a < spZ regs) \/
        ((F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL))
      ltac:(ctc_lia) HAR KT KR
      ltac:(intros a [Ha | Ha]; [left; exact Ha | right; right; exact (HZfr a Ha)])
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    clear KT KR HFr1 HG1; rename KT2 into KT end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msB end.
  pose proof HJ3 as (HAR5 & _).
  rreg HS (1%bv : bv 5) M1. rreg HS (2%bv : bv 5) M2. rreg HS (3%bv : bv 5) M3. rreg HS (4%bv : bv 5) M4.
  rreg HS (10%bv : bv 5) M10. rreg HS (11%bv : bv 5) M11. rreg HS (12%bv : bv 5) M12.
  assert (UspB : spZ (ms_regs msB) = SP1) by (unfold spZ; rewrite M2; exact U33).
  lazymatch type of HS with st_ok _ ?Ev ?ss (restrict _ ?msx) =>
  let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
  eapply (cw_intrin_call B LAWS OSet A_MEMSET AMS W3 Ev ss msx _ STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly3 S3 k
    sg 165 24 539788 K ltac:(let r := eval vm_compute in (firstn 5 (ss_mem ss)) in exact r)) end.
  { exact HS. }
  { reflexivity. }
  { reflexivity. }
  { exact HJ3. }
  { rewrite M10, E11. reflexivity. }
  { rewrite M11. reflexivity. }
  { rewrite M12. reflexivity. }
  { lia. }
  { lia. }
  { lia. }
  { rewrite UspB. unfold ESTACK. lia. }
  { rewrite UspB. lia. }
  { rewrite UspB. exact Hsp1al16. }
  { exact Hsp0al. }
  { rewrite M3, E3. exact Hgp. }
  { rewrite M4, E4. exact Htp. }
  { reflexivity. }
  { lia. }
  { apply ret_ok_even. vm_compute. reflexivity. }
  { intros a Ha. destruct (Htwsg a Ha) as (Haw & _).
    split; [|rewrite UspB; unfold ESTACK; lia].
    eapply (ctc_awr_up B) with (Hbl := Hbl4) (Hfa := Efa3); [|exact Haw].
    intros x Hx; right; exact Hx. }
  { exact Hsgam. }
  { pose proof Hdst as (_ & _ & _ & _ & Hsgra & _).
    eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HAR5) (Hbl := Hbl4) (KT := KT)
      (Happ := HappE); [exact Hosg | lia | exact Hsgam | exact Hsgra]. }
  { intros _. eapply (ctc_obj_hull B LAWS) with (HAR2 := HAR5) (Hbl := Hbl4) (Hfr := Hfr4) (Hfa := Efa3);
      [exact Hosg | lia]. }
  { exact I. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { cbn [ss_mem]; submem_to. }
  { unfold cw_hold in Hsgapp, Hsgimg, HsgF, HFS.
    lazymatch goal with |- Forall ?P ?rs => let rs' := eval vm_compute in rs in change (Forall P rs') end.
    repeat apply Forall_cons; try apply Forall_nil.
    all: split; [intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?U61, ?U38, ?U33, ?B2 in Ha;
             rewrite UspB; unfold ESTACK; split | cbn].
    all: lia. }
  intros regs4 mem4 md4 HJ4 HP4 Ha04 Hset Hkeep Hpres5 Hsbm HS4.
  assert (HIO4 : same_io mdc md4)
    by (eapply same_io_trans; [|apply same_io_materialized; exact Hsbm]; cw_io).
  clear HIO. rename HIO4 into HIO.
  set (PS8 := fun a => sg + 8 <= a < sg + 24).
  assert (HKS8 : forall a, PS8 a -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem4 a) by reflexivity.
  assert (HKF4 : forall a, PK a -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. transitivity (aview tfibsegs (w_H W3) (ms_mem msB) a); [|exact (HKF a Ha)].
    unfold PK in Ha. unfold cw_hold in HsgF. apply Hkeep; [lia | lia | rewrite UspB; unfold ESTACK; lia]. }
  clear HKF. rename HKF4 into HKF.
  (* after the memset: what the call kept; the 24 bytes of sg hold 0xa5 *)
  assert (KT4 : tcj_kept tfibsegs B 8384 lyc Sc W memc W3 mem4 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)).
  { apply (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W3 (ms_mem msB) mem4 (spZ regs) _
      (fun a => sg <= a < sg + 24 \/ SP1 - 4096 <= a < SP1) ltac:(lia) HAR KT).
    - intros a Ha Hx. apply Hkeep; [exact Ha | intros Hy; apply Hx; left; exact Hy
      | rewrite UspB; unfold ESTACK; intros Hy; apply Hx; right; lia].
    - intros a [Ha | Ha]; [right; left; split; [left; exact Ha |] | left; lia].
      intros Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc sg 24 a HAR Htsg Ha Him).
    - exact Hpres5. }
  clear KT. rename KT4 into KT.
  clear HS. rename HS4 into HS. cpw_rebase. norm_ss HS. cw_norm_model.
  clear M1 M2 M3 M4 M10 M11 M12.
  (* ---- 0x83c8c-0x83c98: s11 = SB + dt / 8 and the check of dt's shadow byte (usable) ---- *)
  pose proof HJ4 as (HAR6 & _).
  destruct (ctc_dst_facts B LAWS FFL ly3 S3 W3 mem4 md4 lyc Sc fpos dt 1 HAR6 HFRS Hnin Efa3 Efl3 HPERM Htdt ltac:(lia))
    as (_ & _ & _ & _ & _ & Hdtp).
  assert (Hdtra : range_addressable (aview tfibsegs (w_H W3) mem4) SHADOW_OFF dt 1).
  { pose proof Hddst as (_ & _ & _ & _ & Hdtra0 & _).
    eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HAR6) (Hbl := Hbl4) (KT := KT) (Happ := HappE);
      [exact Hodt | lia | exact Hdtam | exact Hdtra0]. }
  clear SHOK.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 12 0 1] Ev (mrestrict (w_H W3) mem4))
    by (apply Forall_cons; [|apply Forall_nil];
        apply (cw_shent_ra W3 mem4 Ev 12 dt 1 Hdtra Hdtam ltac:(lia) ltac:(lia) ltac:(lia) E12 E32)) end.
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 12 (mkAF 4096 (2 ^ 47 - 2 ^ 23) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E12, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end. norm_ss HS.
  cw_close_win [38; 61]%nat.
  cw_run_to ctc_awr 539804.
  ctc_kp PK HKF.
  ctc_kp PS8 HKS8.
  lazymatch goal with
  | HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
    pose proof (cw_kept_run (fun a => (spZ regs - 8384 <= a < spZ regs))
      Ev rs (w_H W3) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(ctc_kwr)) as KR;
    pose proof (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W3 m1 m2 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)
      (fun a => (spZ regs - 8384 <= a < spZ regs)) ltac:(ctc_lia) HAR KT KR
      ltac:(intros a Ha; left; exact Ha)
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    pose proof (fun x Hx => apresent_grows _ _ _ x HG1 (proj1 (Hdtp x Hx))) as Hdtp2;
    clear KT KR HFr1 HG1; rename KT2 into KT end.
  cw_rebase_tok.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (HAE2 : env_agree 32 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
  assert (U33x : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
  assert (U38x : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61x : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (U12x : bv_unsigned (ew Ev 12) = dt) by (rewrite E12; apply unsigned_lit_small; lia);
  assert (B2x : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity) end.
  clear HAE U33 U38 U61 B2 U38f U61f U60. rename HAE2 into HAE. rename U33x into U33. rename U38x into U38.
  rename U61x into U61. rename U12x into U12. rename B2x into B2.
  (* ---- 0x83c9c sb s6,0(s3): dots := 0xa5; a0 = q, a1 = sg, a2 = dt; jal diginet_counter_text ---- *)
  assert (HWdt : forall a, dt <= a < dt + 1 ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly3 S3) ly3 ((0, fpos) :: own) a).
  { intros a Ha. destruct (Htwdt a Ha) as (Haw & _).
    eapply (ctc_awr_up B) with (Hbl := Hbl4) (Hfa := Efa3); [|exact Haw]. intros x Hx; right; exact Hx. }
  lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 12%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U12; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable tfibsegs); apply Hdtp2; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U12, ?U61, ?U38, ?U33, ?B2; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
      unfold cw_hold in Hdtapp, Hdtimg, HdtF, HFS; repeat split; lia)) as HS3 end.
  clear HS. rename HS3 into HS. norm_ss HS.
  aj_run_to_sh tfibtbl_lib_ok HS HJ4 A_COUNTER_TEXT.
  { ctc_awr. }
  cw_norm_model.
  ctc_kp PK HKF.
  ctc_kp PS8 HKS8.
  lazymatch goal with
  | HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _ |- _ =>
    pose proof (cw_kept_run (fun a => (spZ regs - 8384 <= a < spZ regs) \/ dt <= a < dt + 1)
      Ev rs (w_H W3) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(ctc_kwr)) as KR;
    pose proof (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W3 m1 m2 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)
      (fun a => (spZ regs - 8384 <= a < spZ regs) \/ dt <= a < dt + 1) ltac:(ctc_lia) HAR KT KR
      ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a [Ha | Ha];
            [left; exact Ha | right; left; split; [right; exact Ha |
              let Him := fresh in intros Him; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc dt 1 a HAR Htdt Ha Him)]])
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    clear KT KR HFr1 HG1; rename KT2 into KT end.
  cw_rebase_tok.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (HAE2 : env_agree 32 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
  assert (U33x : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
  assert (U38x : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
  assert (U61x : bv_unsigned (ew Ev 61) = shadow_addr F)
    by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia);
  assert (U12x : bv_unsigned (ew Ev 12) = dt) by (rewrite E12; apply unsigned_lit_small; lia);
  assert (B2x : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity) end.
  clear HAE U33 U38 U61 B2 U12. rename HAE2 into HAE. rename U33x into U33. rename U38x into U38.
  rename U61x into U61. rename U12x into U12. rename B2x into B2.
  (* ---- 0x83cac diginet_counter_text(q, sg, dt) through its contract ---- *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
  pose proof HJ4 as (HAR7 & _).
  rreg HS (1%bv : bv 5) Z1. rreg HS (2%bv : bv 5) Z2. rreg HS (3%bv : bv 5) Z3. rreg HS (4%bv : bv 5) Z4.
  rreg HS (10%bv : bv 5) Z10. rreg HS (11%bv : bv 5) Z11. rreg HS (12%bv : bv 5) Z12.
  assert (UspC : spZ (ms_regs msC) = SP1) by (unfold spZ; rewrite Z2; exact U33).
  assert (C10 : getr (ms_regs msC) 10 = w64 q) by (rewrite Z10; exact E10).
  assert (C11 : getr (ms_regs msC) 11 = w64 sg) by (rewrite Z11; exact E11).
  assert (C12 : getr (ms_regs msC) 12 = w64 dt) by (rewrite Z12; exact E12).
  clear Z2 Z10 Z11 Z12.
  assert (Bstr : cstr_rd tfibsegs W3 (ms_mem msC) (spZ (ms_regs msC)) T_counter_text q tb).
  { rewrite UspC. eapply (ctc_cstr_up B LAWS) with (HAR := HAR) (HAR2 := HAR7) (Hbl := Hbl4) (Hfr := Hfr4)
      (Hfa := Efa3) (KT := KT) (Happ := HappE); [exact Hstr | exact Hoq | exact Hqtb |].
    unfold coff_win, T_counter_text, ESTACK in *. lia. }
  assert (Boq : cobj_ok B ly3 S3 q (Z.of_nat (length tb)))
    by (eapply (ctc_cobj_up B) with (Hbl := Hbl4) (Hfr := Hfr4) (Hfa := Efa3); exact Hoq).
  assert (Bosg : cobj_ok B ly3 S3 sg 8).
  { apply (ctc_cobj_sub B ly3 S3 sg 24); [|lia|lia].
    eapply (ctc_cobj_up B) with (Hbl := Hbl4) (Hfr := Hfr4) (Hfa := Efa3); exact Hosg. }
  assert (Bodt : cobj_ok B ly3 S3 dt 1)
    by (eapply (ctc_cobj_up B) with (Hbl := Hbl4) (Hfr := Hfr4) (Hfa := Efa3); exact Hodt).
  assert (Bdsg : cdst_ok tfibsegs B STK sp0 FP ly S ly3 S3 ((0, fpos) :: own) W3 (ms_mem msC) (spZ (ms_regs msC))
    T_counter_text sg 8).
  { rewrite UspC. eapply (ctc_cdst_up B LAWS) with (HAR := HAR) (HAR2 := HAR7) (Hbl := Hbl4) (Hfr := Hfr4)
      (Hfa := Efa3) (KT := KT) (Happ := HappE); [| exact Hdst | exact Hosg | lia | lia | lia | |].
    - intros x Hx; right; exact Hx.
    - unfold coff_win, T_counter_text, ESTACK. left. lia.
    - intros x Hx. unfold ESTACK. lia. }
  assert (Bddt : cdst_ok tfibsegs B STK sp0 FP ly S ly3 S3 ((0, fpos) :: own) W3 (ms_mem msC) (spZ (ms_regs msC))
    T_counter_text dt 1).
  { rewrite UspC. eapply (ctc_cdst_up B LAWS) with (HAR := HAR) (HAR2 := HAR7) (Hbl := Hbl4) (Hfr := Hfr4)
      (Hfa := Efa3) (KT := KT) (Happ := HappE); [| exact Hddst | exact Hodt | lia | lia | lia | |].
    - intros x Hx; right; exact Hx.
    - unfold coff_win, T_counter_text, ESTACK. left. lia.
    - intros x Hx. unfold ESTACK. lia. }
  destruct (ctc_dst_facts B LAWS FFL ly3 S3 W3 (ms_mem msC) _ lyc Sc fpos sg 24 HAR7 HFRS Hnin Efa3 Efl3 HPERM Htsg
    ltac:(lia)) as (_ & _ & _ & _ & _ & Hsgp7).
  destruct (garr8_of_present tfibsegs (mrestrict (w_H W3) (ms_mem msC)) sg 8) as (sj1 & Bsjl & Bsj).
  { intros a Ha. destruct (proj1 (Hsgp7 a ltac:(lia))) as (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. }
  lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_region_nth Ev ssx msx 0 _ HS eq_refl) as RGd end.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 0 1 (SLit 165) RGd U12 ltac:(cbn; tauto) ltac:(lia)) as Bdj.
  cbn [sv_denot N.to_nat Pos.to_nat] in Bdj. rewrite unsigned_lit_small in Bdj by lia.
  change (165 mod 2 ^ (8 * Z.of_N 1)) with 165 in Bdj. rewrite Z.add_0_r in Bdj. clear RGd.
  assert (Bd1 : sg + 8 <= dt \/ dt + 1 <= sg) by (unfold cw_hold in Hd1; lia).
  assert (Bd2 : q + Z.of_nat (length tb) <= sg \/ sg + 8 <= q) by (unfold cw_hold in Hd2; lia).
  assert (Bd3 : q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) by (unfold cw_hold in Hd3; lia).
  ctc_hide.
  assert (NFfr : forall a, F <= a < F + 64 -> ~ (sg <= a < sg + 8 \/ dt <= a < dt + 1))
    by (unfold cw_hold in HsgF, HdtF; intros a Ha [Hx|Hx]; clear - Ha Hx HsgF HdtF; lia).
  assert (NFsh : forall a, shadow_addr F <= a < shadow_addr F + 8 -> ~ (sg <= a < sg + 8 \/ dt <= a < dt + 1))
    by (unfold cw_hold in Hsgapp, Hdtapp; intros a Ha [Hx|Hx]; clear - Ha Hx Hsgapp Hdtapp HSlo HShi; lia).
  assert (Bimg : cimg_rd tfibsegs B CA_RLO CA_RHI W3 (ms_mem msC) (spZ (ms_regs msC)) T_counter_text [(SEG7TBL, 364)]).
  { rewrite UspC. apply (ctc_cimg_up B lyc Sc W memc W3 (ms_mem msC) 8384 (spZ regs) _ KT _ _ _ _ _ _ Himg);
    [unfold T_counter_text, ESTACK; lia | lia | intros r [<- | []]; left; reflexivity]. }
  assert (Bfr : Z.of_nat (length (frames S3)) <= 8) by (rewrite HFRS; cbn [length]; lia).
  assert (HFA3 : frame_addr ly3 0 fpos = F) by (rewrite Efa3; reflexivity).
  lazymatch type of HS with st_ok _ ?Ev ?ss _ => lazymatch goal with |- SRr _ _ (mkCfg _ ?mdd) _ =>
  eapply (cpw_call W3 Ev ss msC mdd) end end.
  { exact HS. }
  { reflexivity. }
  { eapply CTX.
    { eapply cpw_entry.
      - exact HJ4.
      - rewrite Z1; apply ret_ok_even; vm_compute; reflexivity.
      - unfold raZ; rewrite Z1, unsigned_lit_small by lia; lia.
      - rewrite Z3. transitivity (getr regs 3); [rewrite <- E3; reflexivity | exact Hgp].
      - rewrite Z4. transitivity (getr regs 4); [rewrite <- E4; reflexivity | exact Htp].
      - rewrite UspC; exact Hsp1al16.
      - rewrite UspC; unfold T_counter_text, ESTACK; lia.
      - rewrite UspC; lia.
      - first [assumption | unfold EV_CDC in *; lia].
      - exact HPERM.
      - exact Hlive. }
    all: eassumption. }
  cbv beta; intros W5 c5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfrs5 & HPerm5 & HIO5 & HMLE5 & KT5 & HRl).
  rewrite Z1.
  rewrite UspC in KT5.
  lazymatch type of KT5 with tcj_kept _ _ ?T1 _ _ _ _ _ _ _ _ => let t := eval cbv in T1 in change T1 with t in KT5 end.
  (* the compared bytes, kept by the callee *)
  assert (HKF5 : forall a, PK a -> aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. transitivity (aview tfibsegs (w_H W3) (ms_mem msC) a); [|exact (HKF a Ha)].
    pose proof KT5 as (K1 & _ & _ & K4 & _). unfold PK in Ha. unfold cw_hold in HsgF, HdtF. destruct Ha as [Ha | Ha].
    - apply (K4 0 fpos a); [rewrite HFRS; left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd];
        rewrite HFA3; change (fs_frame_bytes 0) with 64; lia | intros [Hx|Hx]; lia].
    - apply K1; [lia | lia | intros [Hx|Hx]; lia]. }
  clear HKF. rename HKF5 into HKF.
  assert (HKS85 : forall a, PS8 a -> aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W3) mem4 a).
  { intros a Ha. transitivity (aview tfibsegs (w_H W3) (ms_mem msC) a); [|exact (HKS8 a Ha)].
    unfold PS8 in Ha. unfold cw_hold in Hd1. eapply (ctc_obj_keep B) with (KT := KT5);
      [eapply (ctc_cobj_up B) with (Hbl := Hbl4) (Hfr := Hfr4) (Hfa := Efa3); exact Hosg | lia | intros [Hx|Hx]; lia]. }
  clear HKS8. rename HKS85 into HKS8.
  lazymatch type of HS with st_ok _ _ ?ss _ => let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
  jafter_call_keep HS K regs5 (mrestrict (w_H W5) mem5) HP5 [1; 2; 3; 4; 5]%nat HS2 end.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; ctc_kept_c KT5 HJ4 HJ5 HJ0 HFRS HFA0 HFA3. }
  specialize (HS2 HQ). clear HQ.
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok _ (havoc ?E0 ?K0 ?ws0) _ _ =>
  let j := eval vm_compute in (K0 + 4)%nat in
  assert (HA0l : ew (havoc E0 K0 ws0) j = getr regs5 10)
    by exact (ew_havoc_new E0 K0 ws0 4 (Z_to_bv 64 0) ltac:(cbn [length map CLOB]; lia)) end.
  cpw_rebase.
  assert (KTn : tcj_kept tfibsegs B 8384 lyc Sc W memc W5 mem5 (spZ regs) (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)).
  { eapply (cw_kept_cj B LAWS) with (1 := HJ0) (2 := HJ4) (4 := HPERM) (10 := KT) (11 := KT5).
    - rewrite HFRS; apply incl_tl, incl_refl.
    - lia.
    - lia.
    - lia.
    - lia.
    - let a := fresh "a" in let Ha := fresh "Ha" in intros a [Ha | Ha].
      + right; left; split; [left; lia|].
        intros Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc sg 24 a HAR Htsg ltac:(lia) Him).
      + right; left; split; [right; exact Ha|].
        intros Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc dt 1 a HAR Htdt Ha Him). }
  pose proof (eq_trans Hfrs5 HFRS) as HFRSn.
  pose proof (Permutation_trans HPerm5 HPERM) as HPERMn.
  assert (HIOn : same_io mdc md5) by (apply (fun H => same_io_trans _ _ _ H HIO5); cpw_io).
  pose proof (mle_station _ _ _ _ 0 0 MTL HMO HMLE5) as HMOn.
  rewrite Z.add_0_r in HMOn.
  lazymatch type of HJ5 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (?k1 + EV_CDC) =>
    replace (k1 + EV_CDC) with k1 in HJ5 by (unfold EV_CDC; lia) end.
  clear Z1 Z3 Z4 HP5 HIO5 Hfrs5 HPerm5 HMLE5 KT5 HFRS HPERM HIO HMO KT.
  rename KTn into KT. rename HFRSn into HFRS. rename HPERMn into HPERM. rename HIOn into HIO. rename HMOn into HMO.
  cw_norm_model.
  rewrite HCT in HRl. destruct HRl as (HL10 & HL0 & HLn).
  ctc_hide.
  lazymatch type of HA0l with ew ?Ev ?j = _ =>
  assert (EL : ew Ev j = Z_to_bv 64 rl) by (rewrite HA0l, HL10; reflexivity) end.
  clear HA0l.
  (* the bytes the rest of the walk reads, from the callee's return on *)
  set (PT := fun a => PK a \/ PS8 a \/ sg <= a < sg + 8 \/ dt <= a < dt + 1).
  assert (HKT : forall a, PT a -> aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W5) mem5 a) by reflexivity.
  assert (HPT64 : forall a, PT a -> 0 <= a < 2 ^ 64) by (unfold PT, PK, PS8; intros a [Ha|[Ha|[Ha|Ha]]]; [destruct Ha as [Ha|Ha] | ..]; lia).
  assert (HPK64 : forall a, PK a -> 0 <= a < 2 ^ 64) by (intros a Ha; apply HPT64; left; exact Ha).
  assert (HPS64 : forall a, PS8 a -> 0 <= a < 2 ^ 64) by (intros a Ha; apply HPT64; right; left; exact Ha).
  cw_close_win [33; 2]%nat.
  (* ---- 0x83cb0 bne a0,s7: the two codes agree (the agreement premise) ---- *)
  rewrite Hrr in EL.
  cw_branch Hc.
  { exfalso. rewrite branch_ne_U, !U_SOff, EL, E66, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  cw_run_to ctc_awr 539828.
  ctc_closed_fold.
  cw_rebase_tok.
  (* ---- 0x83cb4 bnez s7 ---- *)
  cw_branch Hc.
  + (* rc <> 0: on to 0x83ce0 *)
    assert (Hro : ro <> 0).
    { intros H0. rewrite branch_ne_U, U_SOff, E66, U_SLit, H0 in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    destruct (HLn ltac:(rewrite Hrr; exact Hro)) as (s1 & d1 & Gs1 & Ls1 & Vd1).
    cw_run_to ctc_awr 539872.
    ctc_closed_fold.
    cw_rebase_tok.
    (* ---- at 0x83ce0: the cut C5 of check_text_counter_A_inv.v ---- *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (HAEc : env_agree 32 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
    assert (B2c : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity);
    assert (U38c : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia) end.
    ctc_find_reg HS 38%nat 40 RGfb. ctc_find_reg HS 2%nat (-104) RGsv.
    rreg HS (2%bv : bv 5) X2. rreg HS (9%bv : bv 5) X9. rreg HS (8%bv : bv 5) X8. rreg HS (3%bv : bv 5) X3.
    rreg HS (4%bv : bv 5) X4. rreg HS (18%bv : bv 5) X18. rreg HS (19%bv : bv 5) X19. rreg HS (20%bv : bv 5) X20.
    rreg HS (21%bv : bv 5) X21. rreg HS (24%bv : bv 5) X24. rreg HS (25%bv : bv 5) X25. rreg HS (26%bv : bv 5) X26.
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ ((0, fpos) :: own) ?lyx ?Sx ?Wx ?mx ?mdx _ |- _ =>
      pose proof HJx as (HARc & _) end.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc] end.
    eapply (ctc_c5_done ASF FFL (mkCtc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj) fpos).
    * exact Hpre.
    * eassumption.
    * exact KT.
    * exact HPERM.
    * exact Hnin.
    * exact HMO.
    * cw_io.
    * unfold ctc_common, x_F, x_FL, x_sp. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc
        x_mdc x_k x_regs x_q x_sg x_dt x_tb x_sj x_dj].
      split; [rewrite X2, E33, HSP1e; reflexivity|].
      split; [rewrite X9, E33, HSP1e; reflexivity|].
      split; [rewrite X8, E2; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
      split; [rewrite X3, E3; reflexivity|].
      split; [rewrite X4, E4; reflexivity|].
      split; [rewrite X18, E38; reflexivity|].
      split; [rewrite X19, E12; reflexivity|].
      split; [rewrite X20, E11; reflexivity|].
      split; [rewrite X21, E10; reflexivity|].
      split; [rewrite X24, E32; reflexivity|].
      split; [rewrite X25, E38; reflexivity|].
      split; [rewrite X26, E61; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity|].
      split; [ctc_sv RGsv B2c HAEc 1%nat (1%bv : bv 5) (-8)|].
      split; [ctc_sv RGsv B2c HAEc 8%nat (8%bv : bv 5) (-16)|].
      split; [ctc_sv RGsv B2c HAEc 9%nat (9%bv : bv 5) (-24)|].
      split; [ctc_sv RGsv B2c HAEc 18%nat (18%bv : bv 5) (-32)|].
      split; [ctc_sv RGsv B2c HAEc 19%nat (19%bv : bv 5) (-40)|].
      split; [ctc_sv RGsv B2c HAEc 20%nat (20%bv : bv 5) (-48)|].
      split; [ctc_sv RGsv B2c HAEc 21%nat (21%bv : bv 5) (-56)|].
      split; [ctc_sv RGsv B2c HAEc 22%nat (22%bv : bv 5) (-64)|].
      split; [ctc_sv RGsv B2c HAEc 23%nat (23%bv : bv 5) (-72)|].
      split; [ctc_sv RGsv B2c HAEc 24%nat (24%bv : bv 5) (-80)|].
      split; [ctc_sv RGsv B2c HAEc 25%nat (25%bv : bv 5) (-88)|].
      split; [ctc_sv RGsv B2c HAEc 26%nat (26%bv : bv 5) (-96)|].
      split; [ctc_sv RGsv B2c HAEc 27%nat (27%bv : bv 5) (-104)|].
      apply (rdword_of_val_mem tfibsegs); [|lia].
      eapply (ctc_chunk8 _ _ 38 F _ _ _ _ _ 56 60 FL _ RGfb U38c ltac:(cbn [In]; repeat (first [left; reflexivity | right])) E60); [lia|].
      change (fs_frame_bytes 0) with 64. lia.
    * unfold ctc_P5. cbn [x_sg x_dt].
      exists s1, d1.
      split; [eapply ctc_garr8_kept; [|exact Gs1]; intros x Hx; rewrite Ls1 in Hx; apply HKT; unfold PT; right; right; left; lia|].
      split; [exact Ls1|].
      split.
      { apply ctc_garr8_of_aview; [lia|]. intros i Hi.
        rewrite (HKS8 (sg + 8 + i) ltac:(unfold PS8; lia)).
        replace (sg + 8 + i) with (sg + (8 + i)) by lia. rewrite Hset by lia. reflexivity. }
      split; [eapply cw_val_mem_kept; [|exact Vd1]; intros x Hx; apply HKT; unfold PT; right; right; right; lia|].
      pose proof Hdst as (_ & _ & _ & _ & Hsgra0 & _).
      eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HARc) (Hbl := fun b m Hb => Permutation_in _ (Permutation_sym HPERM) Hb)
        (KT := KT) (Happ := HappE).
      { exact (ctc_cobj_sub B lyc Sc sg 24 (sg + 8) 16 Hosg ltac:(lia) ltac:(lia)). }
      { lia. }
      { unfold amem_range in *. lia. }
      { intros x Hx. apply Hsgra0. lia. }
  + (* rc = 0: 0x83cb8 .. the bcmp wrapper on sg and F + 32 over 8 bytes, the checked dots compare *)
    assert (Hro : ro = 0).
    { destruct (ctc_owed_rc tb ro so dob HOW) as [H0|H0]; [exact H0|]. exfalso.
      rewrite H0 in E66.
      rewrite ?branch_ne_U, ?branch_eq_U, ?U_SOff, ?E66, ?U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    assert (Hrl : rl = 0) by (rewrite Hrr; exact Hro).
    destruct (HL0 Hrl) as (Gs1 & Vd1).
    destruct (Hsd Hrl) as (Esl & Edl).
    destruct (Hwnt Hro) as (Esw & Ev2).
    pose proof (ctc_lib_len tb rl sl dl HCT Hrl) as Ls1.
    rename sl into s1. rename dl into d1.
    cw_run_to ctc_awr 271072.
    ctc_closed_fold.
    cw_rebase_tok.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (HAEd : env_agree 32 (Ereg regs (cw_extra [])) Ev) by env_agree_chain HAE;
    assert (B2d : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity);
    assert (U33d : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
    assert (U38d : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (U61d : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msD end.
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ ((0, fpos) :: own) _ _ W5 (ms_mem msD) _ _ |- _ =>
      rename HJx into HJd end.
    pose proof HJd as (HARd & _).
    destruct (ctc_frame_addr_eq B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJd) as (Efa5 & Efl5).
    pose proof (ctc_frame_present_j B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HJd HFRS HFA0) as (HFp5 & HSp5).
    destruct (ctc_dst_facts B LAWS FFL _ _ W5 (ms_mem msD) _ lyc Sc fpos sg 24 HARd HFRS Hnin Efa5 Efl5 HPERM Htsg ltac:(lia))
      as (_ & _ & _ & _ & _ & Hsgp5).
    assert (Hbl5 : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B _ _))
      by (intros b m Hb; exact (Permutation_in _ (Permutation_sym HPERM) Hb)).
    assert (Hfr5 : incl (frames Sc) (frames _)) by (rewrite HFRS; apply incl_tl, incl_refl).
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc].
    rreg HS (1%bv : bv 5) D1. rreg HS (2%bv : bv 5) D2. rreg HS (3%bv : bv 5) D3. rreg HS (4%bv : bv 5) D4.
    rreg HS (10%bv : bv 5) D10. rreg HS (11%bv : bv 5) D11. rreg HS (12%bv : bv 5) D12.
    assert (UspD : spZ (ms_regs msD) = SP1) by (unfold spZ; rewrite D2; exact U33d).
    assert (G10d : getr (ms_regs msD) 10 = w64 sg) by (rewrite D10; exact E11).
    assert (G11d : getr (ms_regs msD) 11 = w64 (F + 32)) by (rewrite D11, U38d; reflexivity).
    assert (G12d : getr (ms_regs msD) 12 = w64 8) by (rewrite D12; reflexivity).
    (* the eight bytes compare equal: the library's digits and the owed ones agree *)
    assert (Hbytes : forall i, 0 <= i < 8 ->
      aview tfibsegs (w_H W5) (ms_mem msD) (sg + i) = aview tfibsegs (w_H W5) (ms_mem msD) (F + 32 + i)).
    { intros i Hi.
      rewrite (HKT (sg + i) ltac:(unfold PT; right; right; left; lia)).
      rewrite (HKF (F + 32 + i) ltac:(unfold PK; left; lia)).
      rewrite Esl, <- Esw in Gs1.
      destruct (Gs1 (Z.to_nat i) ltac:(rewrite Lsw; lia)) as [V1 _].
      destruct (Gsw (Z.to_nat i) ltac:(rewrite Lsw; lia)) as [V2 _].
      specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
      rewrite Z2Nat.id in V1, V2 by lia. change (Z.of_nat 0) with 0 in V1, V2. rewrite Z.add_0_r in V1, V2.
      unfold aview. rewrite V1, V2. reflexivity. }
    unfold cw_hold in Hsgapp, Hdtapp, HsgF, HdtF, HFS.
    assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
    set (o := SP1 - sp0).
    eapply SRr_bind.
    { eapply (cw_bcmp_at B LAWS A_BCMP ABC W5 (ms_regs msD) (ms_mem msD) STK sp0 FP ly S W0 mem0 md0
        ((0, fpos) :: own) _ _ _ k sg (F + 32) 8 o _).
      - exact HJd.
      - exact G10d.
      - exact G11d.
      - exact G12d.
      - lia.
      - lia.
      - unfold kLowShadowBeg, ASAN_CEIL in *. lia.
      - lia.
      - lia.
      - rewrite UspD. unfold o. lia.
      - unfold o. rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
      - unfold o. lia.
      - unfold o, ESTACK. lia.
      - rewrite D3, E3. exact Hgp.
      - rewrite D4, E4. exact Htp.
      - exact D1.
      - apply ret_ok_even. vm_compute. reflexivity.
      - intros a Ha. split; [apply (aview_some_of_apresent tfibsegs); exact (proj1 (Hsgp5 a ltac:(lia)))|].
        rewrite UspD. unfold ESTACK. lia.
      - intros a Ha. split; [apply (aview_some_of_apresent tfibsegs); apply HFp5; lia|].
        rewrite UspD. unfold ESTACK. lia.
      - intros a Ha. unfold o, ESTACK. lia.
      - intros a Ha. unfold o, ESTACK. lia.
      - unfold amem_range in *. lia.
      - pose proof ASAN_CEIL_range as Hcr. pose proof HFapp as HFa'.
        unfold in_app in HFa'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL in *.
        clear - Hcr HFa' HFq. lia.
      - pose proof Hdst as (_ & _ & _ & _ & Hsgra0 & _).
        eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HARd) (Hbl := Hbl5) (KT := KT) (Happ := HappE).
        + exact (ctc_cobj_sub B lyc Sc sg 24 sg 8 Hosg ltac:(lia) ltac:(lia)).
        + lia.
        + unfold amem_range in *. lia.
        + intros x Hx. apply Hsgra0. lia.
      - intros _. eapply (ctc_obj_hull B LAWS) with (HAR2 := HARd) (Hbl := Hbl5) (Hfr := Hfr5) (Hfa := Efa5).
        + exact (ctc_cobj_sub B lyc Sc sg 24 sg 8 Hosg ltac:(lia) ltac:(lia)).
        + lia.
      - intros x Hx. exists 0. split; [|left; reflexivity].
        assert (Hx8 : x / 8 = F / 8 + 4).
        { rewrite HF8. symmetry. apply (Z.div_unique x 8 (8 * (F / 64) + 4) (x - 8 * (8 * (F / 64) + 4))); [left|]; lia. }
        replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + 4) by (unfold shadow_of_addr, shadow_addr; rewrite Hx8; lia).
        lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
        let rs := eval vm_compute in (ss_mem ssx) in
        let rec go l n := lazymatch l with
          | (YP09.mkRegion (Some 61%nat) 0 _ _ _ _) :: _ => pose proof (st_ok_region_nth Ev ssx msx n _ HS eq_refl) as RG61
          | _ :: ?t => go t constr:(S n) end in go rs 0%nat end.
        pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 4 1 (SLit 0) RG61 U61d ltac:(cbn; tauto) ltac:(lia)) as V4.
        cbn [sv_denot N.to_nat Pos.to_nat] in V4. rewrite unsigned_lit_small in V4 by lia.
        change (0 mod 2 ^ (8 * Z.of_N 1)) with 0 in V4.
        exact (aview_of_val_mem1 tfibsegs _ _ _ _ V4 ltac:(lia)).
      - intros _. apply (shadow_hull_vis_of_frame tfibsegs B LAWS _ _ _ _ _ 0 fpos (F + 32) 8 HARd
          ltac:(rewrite HFRS; left; reflexivity)); try rewrite Efa5; fold F; change (fs_frame_bytes 0) with 64; lia. }
    cbv beta. intros W6 c6 Hwle (-> & regs6 & mem6 & md6 & v & -> & HJ6 & HP6 & Hv & Hcmp & Hkept & Hpres6 & Hsame).
    unfold o, ESTACK in Hkept. replace (sp0 + (SP1 - sp0)) with SP1 in Hkept by lia.
    lazymatch type of HS with st_ok _ _ ?ssv _ =>
      let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
      let l := eval vm_compute in (seq 0 (length (ss_mem ssv))) in
      jafter_call_keep HS K regs6 (mrestrict (w_H W5) mem6) HP6 l HS2 end.
    match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      all: eapply region_kept_aview; [eassumption | | exact Hpres6].
      all: let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha;
           apply Hkept; [unfold shadow_addr, SHADOW_OFF in *; lia | unfold shadow_addr, SHADOW_OFF in *; lia]. }
    specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
    lazymatch type of HS with st_ok _ (havoc ?E0 ?K0 ?ws0) _ _ =>
    let j := eval vm_compute in (K0 + 4)%nat in
    assert (HA0b : ew (havoc E0 K0 ws0) j = getr regs6 10)
      by exact (ew_havoc_new E0 K0 ws0 4 (Z_to_bv 64 0) ltac:(cbn [length map CLOB]; lia)) end.
    cpw_rebase.
    (* what the call kept, and the byte facts, past the wrapper *)
    pose proof (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W5 (ms_mem msD) mem6 (spZ regs) _
      (fun a => SP1 - 8192 <= a < SP1) ltac:(lia) HAR KT
      (fun a Ha Hn => Hkept a Ha Hn) ltac:(intros a Ha; cbv beta in Ha |- *; left; lia) Hpres6) as KT6.
    clear KT. rename KT6 into KT.
    assert (HKT6 : forall a, PT a -> aview tfibsegs (w_H W5) mem6 a = aview tfibsegs (w_H W5) mem5 a).
    { intros a Ha. rewrite <- (HKT a Ha). apply Hkept; [exact (HPT64 a Ha)|].
      unfold PT, PK, PS8 in Ha. lia. }
    clear HKT. rename HKT6 into HKT.
    assert (HKF6 : forall a, PK a -> aview tfibsegs (w_H W5) mem6 a = aview tfibsegs (w_H W3) mem3 a).
    { intros a Ha. rewrite <- (HKF a Ha). apply Hkept; [exact (HPK64 a Ha)|]. unfold PK in Ha. lia. }
    clear HKF. rename HKF6 into HKF.
    assert (HKS86 : forall a, PS8 a -> aview tfibsegs (w_H W5) mem6 a = aview tfibsegs (w_H W3) mem4 a).
    { intros a Ha. rewrite <- (HKS8 a Ha). apply Hkept; [exact (HPS64 a Ha)|]. unfold PS8 in Ha. lia. }
    clear HKS8. rename HKS86 into HKS8.
    assert (HIO6 : same_io mdc md6)
      by (eapply same_io_trans; [|apply same_io_materialized; exact Hsame]; cw_io).
    clear HIO. rename HIO6 into HIO.
    cw_norm_model.
    assert (Hv0 : v = w64 0) by (apply Hcmp; exact Hbytes).
    clear Hcmp Hbytes.
    lazymatch type of HA0b with ew ?Ev ?j = _ =>
      assert (EV0 : ew Ev j = Z_to_bv 64 0) by (rewrite HA0b, Hv, Hv0; reflexivity) end.
    clear HA0b.
    pose proof HJ6 as (HARw & _).
    (* the two dots bytes the walk compares: the library's, and the owed one it saved at SP1 + 55 *)
    assert (Vdc : val_mem tfibsegs (mrestrict (w_H W5) mem6) dt 1 d1)
      by (eapply cw_val_mem_kept; [|exact Vd1]; intros x Hx; apply HKT; unfold PT; right; right; right; lia).
    assert (Vwc : val_mem tfibsegs (mrestrict (w_H W5) mem6) (SP1 + 55) 1 v2)
      by (eapply cw_val_mem_kept; [|exact Vv2]; intros x Hx; apply HKF; unfold PK; right; lia).
    destruct (ctc_vm1 _ _ _ Vdc) as (zd & Hzd & Vzd & Kzd).
    assert (Vzw : val_mem tfibsegs (mrestrict (w_H W5) mem6) (SP1 + 55) 1 zd)
      by (apply Kzd; rewrite Edl, <- Ev2; exact Vwc).
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (U12e : bv_unsigned (ew Ev 12) = dt) by (rewrite E12; apply unsigned_lit_small; lia);
    assert (U33e : bv_unsigned (ew Ev 33) = SP1) by (rewrite E33; apply unsigned_lit_small; lia);
    assert (B2e : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity);
    assert (U38e : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia);
    assert (U61e : bv_unsigned (ew Ev 61) = shadow_addr F)
      by (rewrite E61; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia) end.
    clear U33d U38d U61d B2d.
    (* the dots byte value as a fresh atom: the token engine compares atoms, not open literals *)
    lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
    let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
    pose proof (st_ok_agree tfibsegs K Ev (havoc Ev K [Z_to_bv 64 zd]) ssv msv HS
      (env_agree_havoc_ge K K Ev Ev _ ltac:(lia) (env_agree_refl K Ev)) ltac:(vm_compute; reflexivity)) as HS3;
    assert (EZ : ew (havoc Ev K [Z_to_bv 64 zd]) K = Z_to_bv 64 zd)
      by exact (ew_havoc_new _ K [Z_to_bv 64 zd] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
    clear HS. rename HS3 into HS. cpw_rebase.
    lazymatch type of EZ with ew ?Ev ?K = _ =>
    lazymatch type of HS with st_ok _ ?Ev' ?ssx ?msx =>
    pose proof (st_ok_add_fact tfibsegs Ev' ssx msx K (mkAF 0 255 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EZ, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3 end end.
    clear HS. rename HS3 into HS. norm_ss HS.
    lazymatch type of EZ with ew _ ?K = _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff K 0))]) HS eq_refl
      ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U12e; split; [lia|]; split; [lia|]; split; [intros o' Ho'; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val tfibsegs Ev _ dt 0 1 (SOff K 0) zd);
        [cbn [sv_denot]; rewrite EZ, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | first [change (2 ^ (8 * Z.of_N 1)) with 256; lia | zside | cbn; lia] | first [zside | cbn; lia]
        | rewrite Z.add_0_r; exact Vzd])
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U end;
        change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; unfold shadow_addr, SHADOW_OFF in *;
        repeat split; lia)) as HS3 end end.
    clear HS. rename HS3 into HS. norm_ss HS.
    lazymatch type of EZ with ew _ ?K = _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 33%nat) 55 56 0 0 [YP09.mkChunk 55 (CVal 1 (SOff K 0))]) HS eq_refl
      ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U33e; split; [lia|]; split; [lia|]; split; [intros o' Ho'; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val tfibsegs Ev _ SP1 55 1 (SOff K 0) zd);
        [cbn [sv_denot]; rewrite EZ, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | first [change (2 ^ (8 * Z.of_N 1)) with 256; lia | zside | cbn; lia] | first [zside | cbn; lia]
        | exact Vzw])
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U end;
        change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; unfold shadow_addr, SHADOW_OFF in *;
        repeat split; lia)) as HS3 end end.
    clear HS. rename HS3 into HS. norm_ss HS.
    (* dt's shadow byte, read at 0x83ccc *)
    assert (Hdtra6 : range_addressable (aview tfibsegs (w_H W5) mem6) SHADOW_OFF dt 1).
    { pose proof Hddst as (_ & _ & _ & _ & Hdtra0 & _).
      eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HARw) (Hbl := Hbl5) (KT := KT) (Happ := HappE);
        [exact Hodt | lia | exact Hdtam | exact Hdtra0]. }
    try clear SHOK.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 12 0 1] Ev (mrestrict (w_H W5) mem6))
      by (apply Forall_cons; [|apply Forall_nil];
          apply (cw_shent_ra W5 mem6 Ev 12 dt 1 Hdtra6 Hdtam ltac:(lia) ltac:(lia) ltac:(lia) E12 E32)) end.
    (* 0x83cc8 bnez a0: the wrapper returned 0 *)
    cw_branch Hc.
    { exfalso. rewrite ?branch_ne_U, ?branch_eq_U, ?U_SOff, ?EV0, ?U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    cw_run_to ctc_awr 539852.
    ctc_closed_fold.
    cw_run_to ctc_awr 539860.
    ctc_closed_fold.
    cw_run_to ctc_awr 539868.
    ctc_closed_fold.
    (* 0x83cdc bne a0,a1: both hold the dots atom, so the walk goes on to 0x83ce0 *)
    cw_run_to ctc_awr 539872.
    ctc_closed_fold.
    cw_rebase_tok.
    (* ---- at 0x83ce0: the cut C5 of check_text_counter_A_inv.v ---- *)
    (* name the environment afresh, so that rreg does not unfold its ewsets *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    let Ex := fresh "Ec" in let HEx := fresh "HEc" in
    assert (HAEc : env_agree 32 (Ereg regs (cw_extra [])) Ev) by first [ctc_agree HAEd | ctc_agree HAE];
    remember Ev as Ex eqn:HEx in *; clear HEx end.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (B2c : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity);
    assert (U38c : bv_unsigned (ew Ev 38) = F) by (rewrite E38; apply unsigned_lit_small; lia) end.
    ctc_find_reg HS 38%nat 40 RGfb. ctc_find_reg HS 2%nat (-104) RGsv.
    rreg HS (2%bv : bv 5) X2. rreg HS (9%bv : bv 5) X9. rreg HS (8%bv : bv 5) X8. rreg HS (3%bv : bv 5) X3.
    rreg HS (4%bv : bv 5) X4. rreg HS (18%bv : bv 5) X18. rreg HS (19%bv : bv 5) X19. rreg HS (20%bv : bv 5) X20.
    rreg HS (21%bv : bv 5) X21. rreg HS (24%bv : bv 5) X24. rreg HS (25%bv : bv 5) X25. rreg HS (26%bv : bv 5) X26.
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ ((0, fpos) :: own) ?lyx ?Sx ?Wx ?mx ?mdx _ |- _ =>
      pose proof HJx as (HARc & _) end.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc] end.
    eapply (ctc_c5_done ASF FFL (mkCtc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj) fpos).
    * exact Hpre.
    * eassumption.
    * exact KT.
    * exact HPERM.
    * exact Hnin.
    * exact HMO.
    * cw_io.
    * unfold ctc_common, x_F, x_FL, x_sp. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc
        x_mdc x_k x_regs x_q x_sg x_dt x_tb x_sj x_dj].
      split; [rewrite X2, E33, HSP1e; reflexivity|].
      split; [rewrite X9, E33, HSP1e; reflexivity|].
      split; [rewrite X8, E2; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
      split; [rewrite X3, E3; reflexivity|].
      split; [rewrite X4, E4; reflexivity|].
      split; [rewrite X18, E38; reflexivity|].
      split; [rewrite X19, E12; reflexivity|].
      split; [rewrite X20, E11; reflexivity|].
      split; [rewrite X21, E10; reflexivity|].
      split; [rewrite X24, E32; reflexivity|].
      split; [rewrite X25, E38; reflexivity|].
      split; [rewrite X26, E61; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity|].
      split; [ctc_sv RGsv B2c HAEc 1%nat (1%bv : bv 5) (-8)|].
      split; [ctc_sv RGsv B2c HAEc 8%nat (8%bv : bv 5) (-16)|].
      split; [ctc_sv RGsv B2c HAEc 9%nat (9%bv : bv 5) (-24)|].
      split; [ctc_sv RGsv B2c HAEc 18%nat (18%bv : bv 5) (-32)|].
      split; [ctc_sv RGsv B2c HAEc 19%nat (19%bv : bv 5) (-40)|].
      split; [ctc_sv RGsv B2c HAEc 20%nat (20%bv : bv 5) (-48)|].
      split; [ctc_sv RGsv B2c HAEc 21%nat (21%bv : bv 5) (-56)|].
      split; [ctc_sv RGsv B2c HAEc 22%nat (22%bv : bv 5) (-64)|].
      split; [ctc_sv RGsv B2c HAEc 23%nat (23%bv : bv 5) (-72)|].
      split; [ctc_sv RGsv B2c HAEc 24%nat (24%bv : bv 5) (-80)|].
      split; [ctc_sv RGsv B2c HAEc 25%nat (25%bv : bv 5) (-88)|].
      split; [ctc_sv RGsv B2c HAEc 26%nat (26%bv : bv 5) (-96)|].
      split; [ctc_sv RGsv B2c HAEc 27%nat (27%bv : bv 5) (-104)|].
      apply (rdword_of_val_mem tfibsegs); [|lia].
      eapply (ctc_chunk8 _ _ 38 F _ _ _ _ _ 56 60 FL _ RGfb U38c ltac:(cbn [In]; repeat (first [left; reflexivity | right])) E60); [lia|].
      change (fs_frame_bytes 0) with 64. lia.
    * unfold ctc_P5. cbn [x_sg x_dt].
      exists s1, d1.
      split; [eapply ctc_garr8_kept; [|exact Gs1]; intros x Hx; rewrite Ls1 in Hx; apply HKT; unfold PT; right; right; left; lia|].
      split; [exact Ls1|].
      split.
      { apply ctc_garr8_of_aview; [lia|]. intros i Hi.
        rewrite (HKS8 (sg + 8 + i) ltac:(unfold PS8; lia)).
        replace (sg + 8 + i) with (sg + (8 + i)) by lia. rewrite Hset by lia. reflexivity. }
      split; [eapply cw_val_mem_kept; [|exact Vd1]; intros x Hx; apply HKT; unfold PT; right; right; right; lia|].
      pose proof Hdst as (_ & _ & _ & _ & Hsgra0 & _).
      eapply (ctc_obj_ra B LAWS) with (HAR := HAR) (HAR2 := HARc) (Hbl := fun b m Hb => Permutation_in _ (Permutation_sym HPERM) Hb)
        (KT := KT) (Happ := HappE).
      { exact (ctc_cobj_sub B lyc Sc sg 24 (sg + 8) 16 Hosg ltac:(lia) ltac:(lia)). }
      { lia. }
      { unfold amem_range in *. lia. }
      { intros x Hx. apply Hsgra0. lia. }
Qed.
End d.
End b.
