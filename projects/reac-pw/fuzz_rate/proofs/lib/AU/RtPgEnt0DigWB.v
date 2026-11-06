(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module paths and module names changed; 330 of its 360 lines of code are new or changed and 296 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0DigW.v at 21da95a5fcd3; image B's runs (P1 0x8152c -> 0x81540 with t0 = 4 pinned, the token runs 0x81540 -> 0x81608 with the cell R+0xd8, P2 0x81608 -> 0x8160c with s8 = -8 pinned), registers and class-4 frame, lib/AU/RtPgMemB.v's shadow rows and lib/AU/RtPgW7bBaseB.v's block post w7b_post; names rt7d_ -> rt7bd_, w7_ -> w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the walk of the DIG block of
   ent_build's case 0 (pod.h:237-246, c < 200) from 0x8152c to G = 0x8160c over the journal (no cut state). Proves no
   function (kind: segment lemma).

   HOW. Three runs (lib/AU/RtPgEnt0DigKB.v): P1 0x8152c -> 0x81540 (plain: a2 := 0, a6 := c & 63, r's shadow byte
   shadow_addr F + 28 := 0x04, a1 := a7 := &r), T 0x81540 -> 0x81608 (token, one engine run per v = c mod 64,
   lib/AU/RtPgEnt0DigT0B.v .. T3B.v: the digit loop with its bound test, the reverse copy into ch, the NUL's test
   against the cell R+0xd8 and the NUL), P2 0x81608 -> 0x8160c (plain: shadow_addr F + 28 := 0xf8). rt7bd_walk chains
   them: the journal kept, every register outside a0 .. a7 kept, every byte outside r, ch and shadow_addr F + 28
   kept, the frame's shadow row rsb_PG again, and ch holding the digits of c mod 64 (Pod/Model.v dec64) with their
   NUL. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB RtPgEnt0DefB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgEnt0DigKB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgEnt0DigT0B RtPgEnt0DigT1B RtPgEnt0DigT2B RtPgEnt0DigT3B.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* a register outside a concrete clobber list *)
Ltac rt7bd_notin :=
let H := fresh "H" in intros H; cbv [rt7bd_clobT In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac rt7bd_keep Hk := rewrite Hk by first [cbv; discriminate | rt7bd_notin].
(* a register of a plain run's last state *)
Ltac rt7bd_reg HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  rewrite (st_ok_restrict_reg rsegs _ _ ssf _ r HS);
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the write rights of the plain runs' one region: the frame's own shadow row *)
Ltac rt7bd_awrP U19F Hown :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (rtsb_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat _); [reflexivity | exact U19F | exact Hown | cbn; lia | cbn; lia |];
  apply awr_ok_nil.
(* the frame condition of a plain run: its one window is shadow_addr F + 28 *)
Ltac rt7bd_keptP F U19 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?memc) (mrestrict (w_H ?W) (ms_mem ?ms)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
    intros a Ha Hz;
    refine (w7b_kept_run (rt7bd_wP F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz);
    let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros x (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U19 in Hr; unfold rt7bd_wP; lia
  end.

(* one byte of a region of a run's last state *)
Definition rt7bd_byte_chk (ss : sstate) (i n : nat) (o z : Z) : bool :=
match nth_error (ss_mem ss) i with
| Some r =>
    match YP09.r_base r with
    | Some n' => Nat.eqb n' n && existsb (fun c => rt7bd_lit1 c o z) (YP09.r_chunks r)
    | None => false
    end
| None => false
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rt7bd_byte_of : forall E ss (H : word -> bool) ms i n b o z,
st_ok rsegs E ss (restrict H ms) -> bv_unsigned (ew E n) = b -> rt7bd_byte_chk ss i n o z = true ->
aview rsegs H (ms_mem ms) (b + o) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 z) 0)).
Proof.
intros E ss H ms i n b o z HS Hb Hc. unfold rt7bd_byte_chk in Hc.
destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
destruct r as [rb lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hc.
destruct rb as [n'|]; [|discriminate].
apply andb_prop in Hc as [Hn Hc]. apply Nat.eqb_eq in Hn. subst n'.
pose proof (rtsb_region_nth E ss ms i _ H HS Hi) as Hr.
apply existsb_exists in Hc as (c & Hin & Hl). apply rt7bd_lit1_ok in Hl. subst c.
pose proof (rtsb_chunks E _ n b cs lo hi wlo whi Hr Hb _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H (ms_mem ms)) (b + o) = Some bb) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-. reflexivity.
Qed.

(* a register outside rt7bd_clobT *)
Lemma rt7bd_reg_kept : forall (regs regs' : bvmap 5 word),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rt7bd_clobT -> getr regs' r = getr regs r) ->
forall q, 0 < q < 32 -> existsb (Z.eqb q) [10; 11; 12; 13; 14; 15; 16; 17] = false ->
getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).
Proof.
intros regs regs' Hk q Hq Hn.
assert (Hu : bv_unsigned (Z_to_bv 5 q) = q).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. lia.
- intros Hin. cbv [rt7bd_clobT] in Hin.
  assert (Hin' : In (bv_unsigned (Z_to_bv 5 q)) (map (@bv_unsigned 5) [10; 11; 12; 13; 14; 15; 16; 17]%bv))
    by (apply in_map; exact Hin).
  rewrite Hu in Hin'. cbn [map] in Hin'.
  assert (Hb : existsb (Z.eqb q) [10; 11; 12; 13; 14; 15; 16; 17] = true).
  { apply existsb_exists. exists q. split; [|apply Z.eqb_refl].
    vm_compute in Hin'. exact Hin'. }
  congruence.
Qed.

Section d.
Variable B : asyms.

(* ======================================== P1: 0x8152c -> 0x81540 ======================================== *)
Definition rt7bd_P1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos c : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 13 = w64 c -> 0 <= c < 256 -> getr regs 5 = w64 4 ->
getr regs 23 = w64 (F + 0xe0) ->
SRr rsegs W (cfg_at rsegs RT7BD_P1 regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7BD_LOOP regs memc mdc [11; 12; 16; 17]%bv (rt7bd_wP F)
 (fun regs2 mem2 => getr regs2 12 = w64 0 /\ getr regs2 16 = w64 (c mod 64) /\
   getr regs2 11 = w64 (F + 0xe0) /\ getr regs2 17 = w64 (F + 0xe0) /\
   aview rsegs (w_H W) mem2 (shadow_addr F + 28) = Some 4)).

Lemma rt7bd_P1 : rt7bd_P1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos c HJ Hown HF H19 H13 Hc H5 H23.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
destruct (rt7bd_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin4 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (U19F : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr (frame_addr lyc 4 pos)) by (rewrite U19, HF; reflexivity).
assert (X13 : ew (Ereg regs []) 13 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs [] 13 13%bv eq_refl); exact H13).
assert (X23 : ew (Ereg regs []) 23 = Z_to_bv 64 (F + 0xe0))
  by (rewrite (ew_Ereg_nat regs [] 23 23%bv eq_refl); exact H23).
assert (HSP : st_ok rsegs (Ereg regs []) (rt7bd_ssP RT7BD_P1)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7BD_P1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
pose proof (rt7bd_pin _ _ _ 5%bv 4 HSP eq_refl H5) as HS. clear HSP. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts rt7bd_ssP] in HS.
unfold cfg_at. change (w64 RT7BD_P1) with (Z_to_bv 64 RT7BD_P1).
aj_run_to rt7b_tbl_ok HS HJ RT7BD_LOOP.
- rt7bd_awrP U19F Hown.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | eassumption | ].
  + eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((5%bv : bv 5), SLit 4)] HS);
      [apply env_agree_refl | | vm_compute; reflexivity].
    intros r e [Hin|[]]. injection Hin as <- <-. symmetry. exact H5.
  + rt7bd_keptP F U19.
  + cbv beta. split; [|split; [|split; [|split]]].
    * rt7bd_reg HS (12%bv : bv 5). reflexivity.
    * rt7bd_reg HS (16%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu, U_SLit, (U_atom _ 13 c X13 ltac:(lia)). cbn [zalu_raw]. change (zcanon 63) with 63.
      change (Z.land c 63) with (Z.land c (Z.ones 6)). rewrite Z.land_ones by lia.
      change (2 ^ 6) with 64. pose proof (Z.mod_pos_bound c 64 ltac:(lia)). apply zcanon_id. unfold M64. lia.
    * rt7bd_reg HS (11%bv : bv 5). exact (rtsb_den_atom _ 23 (F + 0xe0) X23 ltac:(lia)).
    * rt7bd_reg HS (17%bv : bv 5). exact (rtsb_den_atom _ 23 (F + 0xe0) X23 ltac:(lia)).
    * refine (eq_trans (rt7bd_byte_of _ _ (w_H W) ms 0 19 (shadow_addr F) 28 4 HS U19 ltac:(vm_compute; reflexivity)) _).
      vm_compute. reflexivity.
Qed.

(* ======================================== P2: 0x81608 -> 0x8160c ======================================== *)
Definition rt7bd_P2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 24 = w64 (-8) ->
SRr rsegs W (cfg_at rsegs RT7BD_P2 regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7BD_G regs memc mdc [] (rt7bd_wP F)
 (fun _ mem2 => aview rsegs (w_H W) mem2 (shadow_addr F + 28) = Some 0xf8)).

Lemma rt7bd_P2 : rt7bd_P2_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos HJ Hown HF H19 H24.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
destruct (rt7bd_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin4 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (U19F : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr (frame_addr lyc 4 pos)) by (rewrite U19, HF; reflexivity).
assert (H24' : getr regs 24 = Z_to_bv 64 RT7BD_M8) by (rewrite H24; apply bv_eq; vm_compute; reflexivity).
assert (HSP : st_ok rsegs (Ereg regs []) (rt7bd_ssP RT7BD_P2)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7BD_P2) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
pose proof (rt7bd_pin _ _ _ 24%bv RT7BD_M8 HSP eq_refl H24') as HS. clear HSP.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts rt7bd_ssP] in HS.
unfold cfg_at. change (w64 RT7BD_P2) with (Z_to_bv 64 RT7BD_P2).
aj_run_to rt7b_tbl_ok HS HJ RT7BD_G.
- rt7bd_awrP U19F Hown.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | eassumption | ].
  + eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((24%bv : bv 5), SLit RT7BD_M8)] HS);
      [apply env_agree_refl | | vm_compute; reflexivity].
    intros r e [Hin|[]]. injection Hin as <- <-. symmetry. exact H24'.
  + rt7bd_keptP F U19.
  + cbv beta.
    refine (eq_trans (rt7bd_byte_of _ _ (w_H W) ms 0 19 (shadow_addr F) 28 RT7BD_M8 HS U19
      ltac:(vm_compute; reflexivity)) _).
    vm_compute. reflexivity.
Qed.

(* ======================================== T: every v < 64 ======================================== *)
Lemma rt7bd_T_all : forall v, 0 <= v < 64 -> rt7bd_T_stmt B v.
Proof.
intros v Hv.
assert (Hx : exists n : nat, (n < 64)%nat /\ v = Z.of_nat n) by (exists (Z.to_nat v); lia).
destruct Hx as (n & Hn & ->). clear Hv.
destruct n as [|n]; [exact (rt7bd_T_0 B)|].
destruct n as [|n]; [exact (rt7bd_T_1 B)|].
destruct n as [|n]; [exact (rt7bd_T_2 B)|].
destruct n as [|n]; [exact (rt7bd_T_3 B)|].
destruct n as [|n]; [exact (rt7bd_T_4 B)|].
destruct n as [|n]; [exact (rt7bd_T_5 B)|].
destruct n as [|n]; [exact (rt7bd_T_6 B)|].
destruct n as [|n]; [exact (rt7bd_T_7 B)|].
destruct n as [|n]; [exact (rt7bd_T_8 B)|].
destruct n as [|n]; [exact (rt7bd_T_9 B)|].
destruct n as [|n]; [exact (rt7bd_T_10 B)|].
destruct n as [|n]; [exact (rt7bd_T_11 B)|].
destruct n as [|n]; [exact (rt7bd_T_12 B)|].
destruct n as [|n]; [exact (rt7bd_T_13 B)|].
destruct n as [|n]; [exact (rt7bd_T_14 B)|].
destruct n as [|n]; [exact (rt7bd_T_15 B)|].
destruct n as [|n]; [exact (rt7bd_T_16 B)|].
destruct n as [|n]; [exact (rt7bd_T_17 B)|].
destruct n as [|n]; [exact (rt7bd_T_18 B)|].
destruct n as [|n]; [exact (rt7bd_T_19 B)|].
destruct n as [|n]; [exact (rt7bd_T_20 B)|].
destruct n as [|n]; [exact (rt7bd_T_21 B)|].
destruct n as [|n]; [exact (rt7bd_T_22 B)|].
destruct n as [|n]; [exact (rt7bd_T_23 B)|].
destruct n as [|n]; [exact (rt7bd_T_24 B)|].
destruct n as [|n]; [exact (rt7bd_T_25 B)|].
destruct n as [|n]; [exact (rt7bd_T_26 B)|].
destruct n as [|n]; [exact (rt7bd_T_27 B)|].
destruct n as [|n]; [exact (rt7bd_T_28 B)|].
destruct n as [|n]; [exact (rt7bd_T_29 B)|].
destruct n as [|n]; [exact (rt7bd_T_30 B)|].
destruct n as [|n]; [exact (rt7bd_T_31 B)|].
destruct n as [|n]; [exact (rt7bd_T_32 B)|].
destruct n as [|n]; [exact (rt7bd_T_33 B)|].
destruct n as [|n]; [exact (rt7bd_T_34 B)|].
destruct n as [|n]; [exact (rt7bd_T_35 B)|].
destruct n as [|n]; [exact (rt7bd_T_36 B)|].
destruct n as [|n]; [exact (rt7bd_T_37 B)|].
destruct n as [|n]; [exact (rt7bd_T_38 B)|].
destruct n as [|n]; [exact (rt7bd_T_39 B)|].
destruct n as [|n]; [exact (rt7bd_T_40 B)|].
destruct n as [|n]; [exact (rt7bd_T_41 B)|].
destruct n as [|n]; [exact (rt7bd_T_42 B)|].
destruct n as [|n]; [exact (rt7bd_T_43 B)|].
destruct n as [|n]; [exact (rt7bd_T_44 B)|].
destruct n as [|n]; [exact (rt7bd_T_45 B)|].
destruct n as [|n]; [exact (rt7bd_T_46 B)|].
destruct n as [|n]; [exact (rt7bd_T_47 B)|].
destruct n as [|n]; [exact (rt7bd_T_48 B)|].
destruct n as [|n]; [exact (rt7bd_T_49 B)|].
destruct n as [|n]; [exact (rt7bd_T_50 B)|].
destruct n as [|n]; [exact (rt7bd_T_51 B)|].
destruct n as [|n]; [exact (rt7bd_T_52 B)|].
destruct n as [|n]; [exact (rt7bd_T_53 B)|].
destruct n as [|n]; [exact (rt7bd_T_54 B)|].
destruct n as [|n]; [exact (rt7bd_T_55 B)|].
destruct n as [|n]; [exact (rt7bd_T_56 B)|].
destruct n as [|n]; [exact (rt7bd_T_57 B)|].
destruct n as [|n]; [exact (rt7bd_T_58 B)|].
destruct n as [|n]; [exact (rt7bd_T_59 B)|].
destruct n as [|n]; [exact (rt7bd_T_60 B)|].
destruct n as [|n]; [exact (rt7bd_T_61 B)|].
destruct n as [|n]; [exact (rt7bd_T_62 B)|].
destruct n as [|n]; [exact (rt7bd_T_63 B)|].
lia.
Qed.

(* ======================================== the walk ======================================== *)
Definition rt7bd_wW (F : Z) : Z -> Prop := fun a => rt7bd_wT F a \/ rt7bd_wP F a.
(* the state at G: the journal, the I/O state, the registers outside rt7bd_clobT, every byte outside r, ch and
   shadow_addr F + 28, the frame's shadow row rsb_PG, and ch holding dec64 (c mod 64) with its NUL *)
Definition rt7bd_wpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (F c : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs RT7BD_G regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io md md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rt7bd_clobT -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ rt7bd_wW F a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem a) /\
rt_fsh rsegs (w_H W) mem2 F rsb_PG /\
rtmb_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 (c mod 64) ++ [Cursor.NUL]).

Lemma rt7bd_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) F pos c R,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 23 = w64 (F + 0xe0) -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 18 = w64 (F + 0xa0) -> getr regs 13 = w64 c -> getr regs 5 = w64 4 -> getr regs 7 = w64 10 ->
getr regs 28 = w64 9 -> getr regs 21 = w64 RSB_MULT10 -> getr regs 24 = w64 (-8) -> getr regs 9 = w64 R ->
alloc_ceiling <= R -> R + 0xe0 <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) mem) (R + 0xd8) 8 (Z.lnot (F + 0xa0) mod 2 ^ 64) ->
0 <= c < 256 ->
rt_fsh rsegs (w_H W) mem F rsb_PG ->
SRr rsegs W (cfg_at rsegs RT7BD_P1 regs mem md) (rt7bd_wpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs mem md F c).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos c R HJ Hown HF H20 H23 H19 H18 H13 H5 H7 H28
  H21 H24 H9 HRc HR1 Hval Hc Hfsh.
destruct (rt7bd_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin4 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (HFR : F + 1024 <= R) by lia.
assert (Hlen : Z.of_nat (length rsb_PG) = 88) by (unfold rsb_PG; rewrite rtmb_sh_len; reflexivity).
assert (Hd : 9223372036854775808 <= Z.lnot (F + 0xa0) mod 2 ^ 64 <= 18446744073709551615)
  by (apply rt7bd_lnot_range; lia).
(* ---- P1 ---- *)
eapply SRr_bind.
{ exact (rt7bd_P1 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem md regs F pos c HJ Hown HF H19 H13 Hc H5 H23). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & _ & H12 & H16 & H11 & H17 & H28s).
assert (Hfsh1 : rt_fsh rsegs (w_H W) m1 F rt7b_PR).
{ replace rt7b_PR with (rtmb_setn rsb_PG 28 1 4) by (unfold rsb_PG, rt7b_PR; rewrite rtmb_sh_r_in; reflexivity).
  apply (rtmb_fsh_set rsegs _ _ _ _ F rsb_PG 28 1 4 Hfsh).
  - intros i Hi. replace i with 28 by lia. exact H28s.
  - intros i Hi Hn. rewrite Hlen in Hi. apply Hm1; [lia | unfold rt7bd_wP; lia]. }
assert (Hval1 : val_mem rsegs (mrestrict (w_H W) m1) (R + 0xd8) 8 (Z.lnot (F + 0xa0) mod 2 ^ 64)).
{ apply (rtsb_val_kept (w_H W) mem m1 (R + 0xd8) 8 _); [|exact Hval].
  intros j Hj. apply Hm1; [lia | unfold rt7bd_wP; lia]. }
assert (R20 : getr r1 20 = w64 SHADOW_OFF) by (rt7bd_keep Hk1; exact H20).
assert (R23 : getr r1 23 = w64 (F + 0xe0)) by (rt7bd_keep Hk1; exact H23).
assert (R19 : getr r1 19 = w64 (shadow_addr F)) by (rt7bd_keep Hk1; exact H19).
assert (R18 : getr r1 18 = w64 (F + 0xa0)) by (rt7bd_keep Hk1; exact H18).
assert (R9 : getr r1 9 = w64 R) by (rt7bd_keep Hk1; exact H9).
assert (R5 : getr r1 5 = w64 4) by (rt7bd_keep Hk1; exact H5).
assert (R7 : getr r1 7 = w64 10) by (rt7bd_keep Hk1; exact H7).
assert (R28 : getr r1 28 = w64 9) by (rt7bd_keep Hk1; exact H28).
assert (R21 : getr r1 21 = w64 RSB_MULT10) by (rt7bd_keep Hk1; exact H21).
assert (R24 : getr r1 24 = w64 (-8)) by (rt7bd_keep Hk1; exact H24).
(* ---- T ---- *)
assert (Hv : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
eapply SRr_bind.
{ exact (rt7bd_T_all (c mod 64) Hv STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W m1 d1 r1 F pos R _ HJ1 Hown HF
    R20 R23 R18 R9 HFR HR1 Hval1 Hd H12 H16 H11 H17 R5 R7 R28 R21 Hfsh1). }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & _ & Hch2).
assert (R19' : getr r2 19 = w64 (shadow_addr F)) by (rt7bd_keep Hk2; exact R19).
assert (R24' : getr r2 24 = w64 (-8)) by (rt7bd_keep Hk2; exact R24).
(* ---- P2 ---- *)
eapply SRr_mono.
{ exact (rt7bd_P2 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W m2 d2 r2 F pos HJ2 Hown HF R19' R24'). }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & _ & H28').
assert (Hkept : forall a, 0 <= a < 2 ^ 64 -> ~ rt7bd_wW F a -> aview rsegs (w_H W) m3 a = aview rsegs (w_H W) mem a).
{ intros a Ha Hn. unfold rt7bd_wW in Hn.
  assert (N1 : ~ rt7bd_wP F a) by tauto. assert (N2 : ~ rt7bd_wT F a) by tauto.
  rewrite (Hm3 a Ha N1), (Hm2 a Ha N2), (Hm1 a Ha N1). reflexivity. }
split; [reflexivity|]. exists r3, m3, d3.
split; [reflexivity|]. split; [exact HJ3|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split.
{ intros r Hr0 Hn.
  assert (N1 : ~ In r ([] : list (bv 5))) by (intros []).
  assert (N2 : ~ In r [11; 12; 16; 17]%bv) by (intros X; apply Hn; cbv [rt7bd_clobT In] in X |- *; tauto).
  rewrite (Hk3 r Hr0 N1), (Hk2 r Hr0 Hn), (Hk1 r Hr0 N2). reflexivity. }
split; [exact Hkept|].
split.
{ assert (E : rtmb_setn rsb_PG 28 1 0xf8 = rsb_PG) by (unfold rsb_PG; rewrite rtmb_sh_r_out; reflexivity).
  rewrite <- E. apply (rtmb_fsh_set rsegs _ _ _ _ F rsb_PG 28 1 0xf8 Hfsh).
  - intros i Hi. replace i with 28 by lia. exact H28'.
  - intros i Hi Hn. rewrite Hlen in Hi. apply Hkept; [lia|].
    unfold rt7bd_wW, rt7bd_wT, rt7bd_wP. lia. }
pose proof (dec64_len (c mod 64)) as Hdl.
eapply (rtmb_bytes_kept rsegs); [exact Hch2|]. intros x Hx.
rewrite length_app in Hx. cbn [length] in Hx.
apply Hm3; [lia | unfold rt7bd_wP; lia].
Qed.
End d.
End b.

Print Assumptions rt7bd_byte_of.
Print Assumptions rt7bd_reg_kept.
Print Assumptions rt7bd_P1.
Print Assumptions rt7bd_P2.
Print Assumptions rt7bd_T_all.
Print Assumptions rt7bd_walk.
