(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths and module names changed; 297 of its 330 lines of code are new or changed and 257 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the walk of the DIG block of
   ent_build's case 0 (pod.h:237-246, c < 200) from 0x813f8 to G = 0x8150c over the journal (no cut state). Proves no
   function (kind: segment lemma).

   HOW. Three runs (lib/A/RtPgEnt0DigK.v): P1 0x813f8 -> 0x8140c (plain: a3 := 0, a4 := c & 0x3f, r's shadow byte
   shadow_addr F + 28 := 0x04, a6 := 1), T 0x8140c -> 0x81504 (token, one engine run per v = c mod 64,
   lib/A/RtPgEnt0DigT0.v .. T3.v: the digits loop, the reverse copy into ch and its NUL), P2 0x81504 -> 0x8150c
   (plain: shadow_addr F + 28 := 0xf8). rt7d_walk chains them: the journal kept, every register outside a0 .. a7, t0
   and t2 kept, every byte outside r, ch and shadow_addr F + 28 kept, the frame's shadow row rs_PG again, and ch
   holding the digits of c mod 64 (Pod/Model.v dec64) with their NUL. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgEnt0Def RtPgEnt0DigK.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgEnt0DigT0 RtPgEnt0DigT1 RtPgEnt0DigT2 RtPgEnt0DigT3.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* a register outside a concrete clobber list *)
Ltac rt7d_notin :=
let H := fresh "H" in intros H; cbv [rt7d_clobT In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac rt7d_keep Hk := rewrite Hk by first [cbv; discriminate | rt7d_notin].
(* a register of a plain run's last state *)
Ltac rt7d_reg HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  rewrite (st_ok_restrict_reg rsegs _ _ ssf _ r HS);
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the write rights of the plain runs' one region: the frame's own shadow row *)
Ltac rt7d_awrP U20F Hown :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (rts_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 20%nat _); [reflexivity | exact U20F | exact Hown | cbn; lia | cbn; lia |];
  apply awr_ok_nil.
(* the frame condition of a plain run: its one window is shadow_addr F + 28 *)
Ltac rt7d_keptP F U20 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?memc) (mrestrict (w_H ?W) (ms_mem ?ms)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
    intros a Ha Hz;
    refine (w7_kept_run (rt7d_wP F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz);
    let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros x (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U20 in Hr; unfold rt7d_wP; lia
  end.

(* one byte of a region of a run's last state *)
Definition rt7d_byte_chk (ss : sstate) (i n : nat) (o z : Z) : bool :=
match nth_error (ss_mem ss) i with
| Some r =>
    match YP09.r_base r with
    | Some n' => Nat.eqb n' n && existsb (fun c => rt7d_lit1 c o z) (YP09.r_chunks r)
    | None => false
    end
| None => false
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rt7d_byte_of : forall E ss (H : word -> bool) ms i n b o z,
st_ok rsegs E ss (restrict H ms) -> bv_unsigned (ew E n) = b -> rt7d_byte_chk ss i n o z = true ->
aview rsegs H (ms_mem ms) (b + o) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 z) 0)).
Proof.
intros E ss H ms i n b o z HS Hb Hc. unfold rt7d_byte_chk in Hc.
destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
destruct r as [rb lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hc.
destruct rb as [n'|]; [|discriminate].
apply andb_prop in Hc as [Hn Hc]. apply Nat.eqb_eq in Hn. subst n'.
pose proof (w7_region_nth E ss (restrict H ms) i _ HS Hi) as Hr.
apply existsb_exists in Hc as (c & Hin & Hl). apply rt7d_lit1_ok in Hl. subst c.
pose proof (rts_chunks E _ n b cs lo hi wlo whi Hr Hb _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H (ms_mem ms)) (b + o) = Some bb) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-. reflexivity.
Qed.

(* a register outside rt7d_clobT *)
Lemma rt7d_reg_kept : forall (regs regs' : bvmap 5 word),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rt7d_clobT -> getr regs' r = getr regs r) ->
forall q, 0 < q < 32 -> existsb (Z.eqb q) [5; 7; 10; 11; 12; 13; 14; 15; 16; 17] = false ->
getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).
Proof.
intros regs regs' Hk q Hq Hn.
assert (Hu : bv_unsigned (Z_to_bv 5 q) = q).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. lia.
- intros Hin. cbv [rt7d_clobT] in Hin.
  assert (Hin' : In (bv_unsigned (Z_to_bv 5 q)) (map (@bv_unsigned 5) [5; 7; 10; 11; 12; 13; 14; 15; 16; 17]%bv))
    by (apply in_map; exact Hin).
  rewrite Hu in Hin'. cbn [map] in Hin'.
  assert (Hb : existsb (Z.eqb q) [5; 7; 10; 11; 12; 13; 14; 15; 16; 17] = true).
  { apply existsb_exists. exists q. split; [|apply Z.eqb_refl].
    vm_compute in Hin'. exact Hin'. }
  congruence.
Qed.

Section d.
Variable B : asyms.

(* ======================================== P1: 0x813f8 -> 0x8140c ======================================== *)
Definition rt7d_P1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos c : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (3, pos) own -> F = frame_addr lyc 3 pos ->
getr regs 20 = w64 (shadow_addr F) -> getr regs 10 = w64 c -> 0 <= c < 256 ->
SRr rsegs W (cfg_at rsegs RT7D_P1 regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7D_LOOP regs memc mdc [10; 13; 14; 16]%bv (rt7d_wP F)
 (fun regs2 mem2 => getr regs2 13 = w64 0 /\ getr regs2 14 = w64 (c mod 64) /\ getr regs2 16 = w64 1 /\
   aview rsegs (w_H W) mem2 (shadow_addr F + 28) = Some 4)).

Lemma rt7d_P1 : rt7d_P1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos c HJ Hown HF H20 H10 Hc.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
destruct (rt7d_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin3 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (U20 : bv_unsigned (ew (Ereg regs []) 20) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia. }
assert (U20F : bv_unsigned (ew (Ereg regs []) 20) = shadow_addr (frame_addr lyc 3 pos)) by (rewrite U20, HF; reflexivity).
assert (X10 : ew (Ereg regs []) 10 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs []) (rt7d_ssP RT7D_P1)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7D_P1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtm_rw_region rsegs _ _ _ 20%nat (shadow_addr F)); [exact U20 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
unfold cfg_at. change (w64 RT7D_P1) with (Z_to_bv 64 RT7D_P1).
aj_run_to rt7_tbl_ok HS HJ RT7D_LOOP.
- rt7d_awrP U20F Hown.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | eassumption | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + rt7d_keptP F U20.
  + cbv beta. split; [|split; [|split]].
    * rt7d_reg HS (13%bv : bv 5). reflexivity.
    * rt7d_reg HS (14%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu, U_SLit, (U_atom _ 10 c X10 ltac:(lia)). cbn [zalu_raw]. change (zcanon 63) with 63.
      change (Z.land c 63) with (Z.land c (Z.ones 6)). rewrite Z.land_ones by lia.
      change (2 ^ 6) with 64. pose proof (Z.mod_pos_bound c 64 ltac:(lia)). apply zcanon_id. unfold M64. lia.
    * rt7d_reg HS (16%bv : bv 5). reflexivity.
    * refine (eq_trans (rt7d_byte_of _ _ (w_H W) ms 0 20 (shadow_addr F) 28 4 HS U20 ltac:(vm_compute; reflexivity)) _).
      vm_compute. reflexivity.
Qed.

(* ======================================== P2: 0x81504 -> 0x8150c ======================================== *)
Definition rt7d_P2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (3, pos) own -> F = frame_addr lyc 3 pos ->
getr regs 20 = w64 (shadow_addr F) ->
SRr rsegs W (cfg_at rsegs RT7D_P2 regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7D_G regs memc mdc [10]%bv (rt7d_wP F)
 (fun _ mem2 => aview rsegs (w_H W) mem2 (shadow_addr F + 28) = Some 0xf8)).

Lemma rt7d_P2 : rt7d_P2_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos HJ Hown HF H20.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
destruct (rt7d_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin3 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (U20 : bv_unsigned (ew (Ereg regs []) 20) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia. }
assert (U20F : bv_unsigned (ew (Ereg regs []) 20) = shadow_addr (frame_addr lyc 3 pos)) by (rewrite U20, HF; reflexivity).
assert (HS : st_ok rsegs (Ereg regs []) (rt7d_ssP RT7D_P2)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7D_P2) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtm_rw_region rsegs _ _ _ 20%nat (shadow_addr F)); [exact U20 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
unfold cfg_at. change (w64 RT7D_P2) with (Z_to_bv 64 RT7D_P2).
aj_run_to rt7_tbl_ok HS HJ RT7D_G.
- rt7d_awrP U20F Hown.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | eassumption | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + rt7d_keptP F U20.
  + cbv beta.
    refine (eq_trans (rt7d_byte_of _ _ (w_H W) ms 0 20 (shadow_addr F) 28 18446744073709551608 HS U20
      ltac:(vm_compute; reflexivity)) _).
    vm_compute. reflexivity.
Qed.

(* ======================================== T: every v < 64 ======================================== *)
Lemma rt7d_T_all : forall v, 0 <= v < 64 -> rt7d_T_stmt B v.
Proof.
intros v Hv.
assert (Hx : exists n : nat, (n < 64)%nat /\ v = Z.of_nat n) by (exists (Z.to_nat v); lia).
destruct Hx as (n & Hn & ->). clear Hv.
destruct n as [|n]; [exact (rt7d_T_0 B)|].
destruct n as [|n]; [exact (rt7d_T_1 B)|].
destruct n as [|n]; [exact (rt7d_T_2 B)|].
destruct n as [|n]; [exact (rt7d_T_3 B)|].
destruct n as [|n]; [exact (rt7d_T_4 B)|].
destruct n as [|n]; [exact (rt7d_T_5 B)|].
destruct n as [|n]; [exact (rt7d_T_6 B)|].
destruct n as [|n]; [exact (rt7d_T_7 B)|].
destruct n as [|n]; [exact (rt7d_T_8 B)|].
destruct n as [|n]; [exact (rt7d_T_9 B)|].
destruct n as [|n]; [exact (rt7d_T_10 B)|].
destruct n as [|n]; [exact (rt7d_T_11 B)|].
destruct n as [|n]; [exact (rt7d_T_12 B)|].
destruct n as [|n]; [exact (rt7d_T_13 B)|].
destruct n as [|n]; [exact (rt7d_T_14 B)|].
destruct n as [|n]; [exact (rt7d_T_15 B)|].
destruct n as [|n]; [exact (rt7d_T_16 B)|].
destruct n as [|n]; [exact (rt7d_T_17 B)|].
destruct n as [|n]; [exact (rt7d_T_18 B)|].
destruct n as [|n]; [exact (rt7d_T_19 B)|].
destruct n as [|n]; [exact (rt7d_T_20 B)|].
destruct n as [|n]; [exact (rt7d_T_21 B)|].
destruct n as [|n]; [exact (rt7d_T_22 B)|].
destruct n as [|n]; [exact (rt7d_T_23 B)|].
destruct n as [|n]; [exact (rt7d_T_24 B)|].
destruct n as [|n]; [exact (rt7d_T_25 B)|].
destruct n as [|n]; [exact (rt7d_T_26 B)|].
destruct n as [|n]; [exact (rt7d_T_27 B)|].
destruct n as [|n]; [exact (rt7d_T_28 B)|].
destruct n as [|n]; [exact (rt7d_T_29 B)|].
destruct n as [|n]; [exact (rt7d_T_30 B)|].
destruct n as [|n]; [exact (rt7d_T_31 B)|].
destruct n as [|n]; [exact (rt7d_T_32 B)|].
destruct n as [|n]; [exact (rt7d_T_33 B)|].
destruct n as [|n]; [exact (rt7d_T_34 B)|].
destruct n as [|n]; [exact (rt7d_T_35 B)|].
destruct n as [|n]; [exact (rt7d_T_36 B)|].
destruct n as [|n]; [exact (rt7d_T_37 B)|].
destruct n as [|n]; [exact (rt7d_T_38 B)|].
destruct n as [|n]; [exact (rt7d_T_39 B)|].
destruct n as [|n]; [exact (rt7d_T_40 B)|].
destruct n as [|n]; [exact (rt7d_T_41 B)|].
destruct n as [|n]; [exact (rt7d_T_42 B)|].
destruct n as [|n]; [exact (rt7d_T_43 B)|].
destruct n as [|n]; [exact (rt7d_T_44 B)|].
destruct n as [|n]; [exact (rt7d_T_45 B)|].
destruct n as [|n]; [exact (rt7d_T_46 B)|].
destruct n as [|n]; [exact (rt7d_T_47 B)|].
destruct n as [|n]; [exact (rt7d_T_48 B)|].
destruct n as [|n]; [exact (rt7d_T_49 B)|].
destruct n as [|n]; [exact (rt7d_T_50 B)|].
destruct n as [|n]; [exact (rt7d_T_51 B)|].
destruct n as [|n]; [exact (rt7d_T_52 B)|].
destruct n as [|n]; [exact (rt7d_T_53 B)|].
destruct n as [|n]; [exact (rt7d_T_54 B)|].
destruct n as [|n]; [exact (rt7d_T_55 B)|].
destruct n as [|n]; [exact (rt7d_T_56 B)|].
destruct n as [|n]; [exact (rt7d_T_57 B)|].
destruct n as [|n]; [exact (rt7d_T_58 B)|].
destruct n as [|n]; [exact (rt7d_T_59 B)|].
destruct n as [|n]; [exact (rt7d_T_60 B)|].
destruct n as [|n]; [exact (rt7d_T_61 B)|].
destruct n as [|n]; [exact (rt7d_T_62 B)|].
destruct n as [|n]; [exact (rt7d_T_63 B)|].
lia.
Qed.

(* ======================================== the walk ======================================== *)
Definition rt7d_wW (F : Z) : Z -> Prop := fun a => rt7d_wT F a \/ rt7d_wP F a.
(* the state at G: the journal, the I/O state, the registers outside rt7d_clobT, every byte outside r, ch and
   shadow_addr F + 28, the frame's shadow row rs_PG, and ch holding dec64 (c mod 64) with its NUL *)
Definition rt7d_wpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (F c : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs RT7D_G regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io md md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rt7d_clobT -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ rt7d_wW F a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem a) /\
rt_fsh rsegs (w_H W) mem2 F rs_PG /\
rtm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 (c mod 64) ++ [Cursor.NUL]).

Lemma rt7d_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
In (3, pos) own -> F = frame_addr lyc 3 pos ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (F + 0xe0) -> getr regs 20 = w64 (shadow_addr F) ->
getr regs 22 = w64 (F + 0xa0) -> getr regs 10 = w64 c -> getr regs 17 = w64 10 -> getr regs 5 = w64 9 ->
getr regs 7 = w64 RS_MULT10 -> 0 <= c < 256 ->
rt_fsh rsegs (w_H W) mem F rs_PG ->
SRr rsegs W (cfg_at rsegs RT7D_P1 regs mem md) (rt7d_wpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs mem md F c).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos c HJ Hown HF H18 H19 H20 H22 H10 H17 H5 H7 Hc
  Hfsh.
destruct (rt7d_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
  as (Hin3 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp).
assert (Hlen : Z.of_nat (length rs_PG) = 56) by (rewrite rt7_PG_sh, rtm_sh_len; reflexivity).
(* ---- P1 ---- *)
eapply SRr_bind.
{ exact (rt7d_P1 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem md regs F pos c HJ Hown HF H20 H10 Hc). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & _ & H13 & H14 & H16 & H28).
assert (Hfsh1 : rt_fsh rsegs (w_H W) m1 F rt7_PR).
{ replace rt7_PR with (rtm_setn rs_PG 28 1 4) by (rewrite rt7_PG_sh, rtm_sh_r_in; reflexivity).
  apply (rtm_fsh_set rsegs _ _ _ _ F rs_PG 28 1 4 Hfsh).
  - intros i Hi. replace i with 28 by lia. exact H28.
  - intros i Hi Hn. rewrite Hlen in Hi. apply Hm1; [lia | unfold rt7d_wP; lia]. }
assert (R18 : getr r1 18 = w64 SHADOW_OFF) by (rt7d_keep Hk1; exact H18).
assert (R19 : getr r1 19 = w64 (F + 0xe0)) by (rt7d_keep Hk1; exact H19).
assert (R20 : getr r1 20 = w64 (shadow_addr F)) by (rt7d_keep Hk1; exact H20).
assert (R22 : getr r1 22 = w64 (F + 0xa0)) by (rt7d_keep Hk1; exact H22).
assert (R17 : getr r1 17 = w64 10) by (rt7d_keep Hk1; exact H17).
assert (R5 : getr r1 5 = w64 9) by (rt7d_keep Hk1; exact H5).
assert (R7 : getr r1 7 = w64 RS_MULT10) by (rt7d_keep Hk1; exact H7).
(* ---- T ---- *)
assert (Hv : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
eapply SRr_bind.
{ exact (rt7d_T_all (c mod 64) Hv STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W m1 d1 r1 F pos HJ1 Hown HF
    R18 R19 R22 H13 H14 H16 R17 R5 R7 Hfsh1). }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & _ & Hch2).
assert (R20' : getr r2 20 = w64 (shadow_addr F)) by (rt7d_keep Hk2; exact R20).
(* ---- P2 ---- *)
eapply SRr_mono.
{ exact (rt7d_P2 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W m2 d2 r2 F pos HJ2 Hown HF R20'). }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & _ & H28').
assert (Hkept : forall a, 0 <= a < 2 ^ 64 -> ~ rt7d_wW F a -> aview rsegs (w_H W) m3 a = aview rsegs (w_H W) mem a).
{ intros a Ha Hn. unfold rt7d_wW in Hn.
  assert (N1 : ~ rt7d_wP F a) by tauto. assert (N2 : ~ rt7d_wT F a) by tauto.
  rewrite (Hm3 a Ha N1), (Hm2 a Ha N2), (Hm1 a Ha N1). reflexivity. }
split; [reflexivity|]. exists r3, m3, d3.
split; [reflexivity|]. split; [exact HJ3|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split.
{ intros r Hr0 Hn.
  assert (N1 : ~ In r [10]%bv) by (intros X; apply Hn; cbv [rt7d_clobT In] in X |- *; tauto).
  assert (N2 : ~ In r [10; 13; 14; 16]%bv) by (intros X; apply Hn; cbv [rt7d_clobT In] in X |- *; tauto).
  rewrite (Hk3 r Hr0 N1), (Hk2 r Hr0 Hn), (Hk1 r Hr0 N2). reflexivity. }
split; [exact Hkept|].
split.
{ assert (E : rtm_setn rs_PG 28 1 0xf8 = rs_PG) by (rewrite rt7_PG_sh, rtm_sh_r_out; reflexivity).
  rewrite <- E. apply (rtm_fsh_set rsegs _ _ _ _ F rs_PG 28 1 0xf8 Hfsh).
  - intros i Hi. replace i with 28 by lia. exact H28'.
  - intros i Hi Hn. rewrite Hlen in Hi. apply Hkept; [lia|].
    unfold rt7d_wW, rt7d_wT, rt7d_wP. lia. }
pose proof (dec64_len (c mod 64)) as Hd.
eapply (rtm_bytes_kept rsegs); [exact Hch2|]. intros x Hx.
rewrite length_app in Hx. cbn [length] in Hx.
apply Hm3; [lia | unfold rt7d_wP; lia].
Qed.
End d.
End b.

Print Assumptions rt7d_P1.
Print Assumptions rt7d_P2.
Print Assumptions rt7d_T_all.
Print Assumptions rt7d_walk.
