(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 289 of its 361 lines of code are new or changed and 1419 lines of the source are left out. *)
(* reac_segconf_find on fuzz_segconf.asan (image A, 0x894ec, 42 instructions): the proof of
   reac_segconf_find_contract (lib/A/Prog/reac_segconf_find_c.v) from the contract of the strcmp wrapper
   (row 17 of provenance/evidence/interceptors/INTERFACE-A-interceptors.md: RtString.astrcmp_realizes, at the listing's call
   target pa_sigma SS___interceptor_trampoline_strcmp).
   reac_segconf_find_s1.v holds the entry 0x894ec-0x89540 (with the instrumented check of c->n removed by the
   shadow token of the block), the epilogue 0x8956c-0x89580, the cut and the seeds. This file steps the loop's
   one call through PaArt's aj_art_at, closes the loop by induction on the entries left, and composes.
   Written new (the walk lane); the control flow is the plain / UBSan owner's plain walk lib/Prog/reac_segconf_find.v at
   the plain / UBSan integration commit 440d61eaa8c8, the ASan shape is plugin-hostd/fuzz_command's lib/A/Prog/rec_calls_equal.v
   at origin/ossv/recipes 501c0d516c69. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaNoChain PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_lem reac_segconf_find_c reac_segconf_find_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma fnd_kept_widen : forall rd1 rd2 lo hi lo' hi', fnd_kept rd1 rd2 lo hi -> lo' <= lo -> hi <= hi' ->
fnd_kept rd1 rd2 lo' hi'.
Proof. intros rd1 rd2 lo hi lo' hi' H Hl Hh a Ha Hn. apply H; [exact Ha | lia]. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation FND_STK := SegInstA.STK_reac_segconf_find.

(* the two walk tactics of reac_segconf_find_s1.v (an Ltac is local to its section, so they are restated here) *)
Ltac fnd_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m
    | _ => idtac end end.
Ltac fnd_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : fnd_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.

Section e.
Variable B : asyms.
(* the wrapper this function calls, at the listing's call target: row 17 of the interceptor layer's interface *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
(* the shadow GOT word and the shadow-base cell of the listing, and the runtime's errno window *)
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low errno_low.

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (RLO RHI c name : Z) (rcs : rconf) (nm : list Z).
Hypothesis HPRE : afn_pre SEGS B FND_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis Hc64 : 0 <= c < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 name.
Hypothesis Hnm64 : 0 <= name < 2 ^ 64.
Hypothesis HQP : query_pre SEGS B ly S (rdW W mem) c name rcs nm.

#[local] Notation QQ := (fnd_Q B ly S W regs mem md c rcs nm).
#[local] Notation LHP := (fnd_LHP B ly S W regs mem md c name rcs nm).

(* ---------- one pass of the loop 0x89544 .. 0x89564, with the strcmp call at 0x8954c ---------- *)
Lemma fnd_loop_step : forall k regs1 mem1 md1,
  ((Datatypes.S k < length (rc_seg rcs))%nat -> forall r m d, LHP (Datatypes.S k) r m d ->
     SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + FND_LH)) m (seg_rom SEGS)) d) QQ) ->
  LHP k regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)) md1) QQ.
Proof using ART ASTRCMP HPRE HQP HROD Hc64 Hnm64.
intros k regs1 mem1 md1 NXT ((HJ & HK & HFR & R2 & RK) & Hk & RF & R8 & R9 & R18).
pose proof RK as RKall. pose proof HJ as HJ0.
destruct RK as (RK3 & RK4 & RK19 & RK20 & RK21 & RK22 & RK23 & RK24 & RK25 & RK26 & RK27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fnd_sp B ly S W regs mem md ch c name HPRE Hc64 Hnm64) as (Hal16 & Hlo & Hhi & Hslo & Hstkw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : FND_STK = 8224) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (fnd_c_facts B ly S W regs mem md ch c name rcs nm HPRE Hc64 Hnm64 HQP)
  as (Hc4096 & Hcceil & Hc16 & Hcoff & Hcband).
pose proof (fnd_name_facts B ly S W regs mem md ch c name rcs nm HPRE Hc64 Hnm64 HQP) as (Hn4096 & Hnceil).
pose proof (fnd_n_le B ly S W mem c name rcs nm HQP) as HNle.
pose proof (fnd_name_len B ly S W mem c name rcs nm HQP) as HNmlen.
destruct (fnd_blk B ly S W mem c name rcs nm HQP) as (bs & HB & HE & HL & _).
destruct (fnd_seg_name (rdW W mem) c bs rcs k HB HE Hk) as (sx & HX & HXN & HXZ & HNN & HXL).
pose proof (fnd_name_str B ly S W mem c name rcs nm HQP) as HNstr.
destruct (sa_strz_bytes SEGS (w_H W) mem name nm (proj1 HNstr)) as (HY & HYN & HYZ).
pose proof (fnd_c_addr B ly S W mem c name rcs nm HQP) as CA.
pose proof (fnd_name_addr B ly S W mem c name rcs nm HQP) as NA.
(* the model step: entry k is the one the loop tests now *)
rewrite (seg_query_facts.sq_find_go_step _ nm k Hk) in RF. fold (r_seg rcs k) in RF.
(* the seed of the loop head and the run to the call *)
destruct (fnd_LH_seed B ly S W regs mem md ch c name HPRE Hc64 Hnm64 regs1 mem1 R2) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 ([] : list word)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs1 ([] : list word))) n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 ([] : list word))) 2) = spZ regs - 32)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. pose proof (EE 9%nat 9%bv eq_refl) as E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18.
remember (Eimg (Ereg regs1 ([] : list word))) as E eqn:HEenv. clear HEenv.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
fnd_md.
fnd_keep_empty HFr KEEP1 (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
prreg HS (11%bv : bv 5) P11. prreg HS (18%bv : bv 5) P18.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEPc : fnd_kept (rdW W mem) (rdW W mT0) (spZ regs - FND_STK) (spZ regs))
  by (apply (fnd_kept_trans _ _ _ _ _ _ _ HK KEEP1); lia).
assert (HspT : spZ rT0 = spZ regs + -32) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, RK3; exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, RK4; exact Htp).
assert (P10' : getr rT0 10 = w64 (c + 356 * Z.of_nat k)) by (rewrite P10, E8; exact R8).
assert (P11' : getr rT0 11 = w64 name) by (rewrite P11, E9; exact R9).
(* the two strings the wrapper reads, at the call's memory *)
assert (HXc : sa_bytes (rdW W mT0) (c + 356 * Z.of_nat k) (sx ++ [Z_to_bv 8 0]))
  by (apply (fnd_bytes_kept (rdW W mem) _ (spZ regs - FND_STK) (spZ regs));
      [exact KEEPc | exact HX | lia | rewrite length_app; cbn [length]; lia
       | left; rewrite length_app; cbn [length]; lia]).
assert (HYc : sa_bytes (rdW W mT0) name (seg_spec.zb nm ++ [ZB0]))
  by (apply (fnd_bytes_kept (rdW W mem) _ (spZ regs - FND_STK) (spZ regs));
      [exact KEEPc | exact HY | lia
       | unfold seg_spec.zb; rewrite length_app, length_map; cbn [length]; lia
       | left; unfold seg_spec.zb; rewrite length_app, length_map; cbn [length]; lia]).
assert (CAm : sa_addr (rdW W mT0) c 16616)
  by (apply (fnd_addr_kept (rdW W mem) _ (spZ regs - FND_STK) (spZ regs)); [exact KEEPc | exact CA | lia ..]).
assert (NAm : sa_addr (rdW W mT0) name (Z.of_nat (length nm) + 1))
  by (apply (fnd_addr_kept (rdW W mem) _ (spZ regs - FND_STK) (spZ regs)); [exact KEEPc | exact NA | lia ..]).
pose proof (fnd_sa_addr_sub (rdW W mT0) c 16616 (c + 356 * Z.of_nat k) (Z.of_nat (length sx) + 1)
  CAm ltac:(lia) ltac:(lia) ltac:(lia)) as CAk.
assert (STRx : astr_at SEGS W mT0 (c + 356 * Z.of_nat k) sx) by (split; [exact HXc | exact HXN]).
assert (STRy : astr_at SEGS W mT0 name (seg_spec.zb nm)) by (split; [exact HYc | exact HYN]).
assert (RDx : aread_ok SEGS (2 * ESTACK) W rT0 mT0 (c + 356 * Z.of_nat k) (astr_len sx + 1)).
{ destruct CAk as (A0 & A1 & A2 & A3 & A4). unfold aread_ok, astr_len.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - replace a with (c + 356 * Z.of_nat k + Z.of_nat (Z.to_nat (a - (c + 356 * Z.of_nat k)))) by lia.
      rewrite HXc by (rewrite length_app; cbn [length]; lia). discriminate.
    - unfold ascratch_stk. rewrite HspT. lia. }
  split; [exact A2|]. split; [exact A3 | exact A4]. }
assert (RDy : aread_ok SEGS (2 * ESTACK) W rT0 mT0 name (astr_len (seg_spec.zb nm) + 1)).
{ destruct NAm as (A0 & A1 & A2 & A3 & A4). unfold aread_ok, astr_len, seg_spec.zb.
  rewrite length_map. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - replace a with (name + Z.of_nat (Z.to_nat (a - name))) by lia.
      rewrite HYc by (unfold seg_spec.zb; rewrite length_app, length_map; cbn [length]; lia). discriminate.
    - unfold ascratch_stk. rewrite HspT. lia. }
  split; [exact A2|]. split; [exact A3 | exact A4]. }
assert (TLx : atail_vis SEGS W mT0 (c + 356 * Z.of_nat k + astr_len sx)).
{ intros a Ha. unfold astr_len in Ha.
  pose proof (Z.mod_pos_bound (c + 356 * Z.of_nat k + Z.of_nat (length sx)) 8 ltac:(lia)) as Hm8.
  rewrite (KEEPc a ltac:(lia) ltac:(lia)).
  exact (fnd_blk_vis B ly S W mem c name rcs nm Hc64 Hnm64 HQP a ltac:(lia)). }
assert (TLy : atail_vis SEGS W mT0 (name + astr_len (seg_spec.zb nm))).
{ unfold astr_len, seg_spec.zb. rewrite length_map. intros a Ha.
  pose proof (Z.mod_pos_bound (name + Z.of_nat (length nm)) 8 ltac:(lia)) as Hm8.
  rewrite (KEEPc a ltac:(lia) ltac:(lia)). exact (proj2 HNstr a Ha). }
assert (ROM : rt_rom_view SEGS B W mT0).
{ intros a Ha Ho He. destruct Ha as (sg & Hsg & Hw & Hr).
  assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg) as HR. unfold kImgEnd in HR.
  rewrite (KEEPc a ltac:(lia) ltac:(lia)).
  apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He]. }
(* 0x8954c: strcmp(c + 356 k, name) *)
eapply SRr_bind.
{ eapply (ART (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strcmp)
    W rT0 mT0 FND_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-32) (Z_to_bv 64 (BASE + FND_RET)) _
    HJ HspT eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1
    (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx ly S W rT0 mT0 _ (c + 356 * Z.of_nat k) name sx (seg_spec.zb nm)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) FND_STK (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-32)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'.
  - exact P11'.
  - lia.
  - lia.
  - exact STRx.
  - exact STRy.
  - exact RDx.
  - exact RDy.
  - exact TLx.
  - exact TLy.
  - exact ROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs - 32) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : YCbn.sh_ok SEGS fnd_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : fnd_kept (rdW W mT0) (rdW W mem2) (spZ regs - FND_STK) (spZ regs - 32))
  by (intros x0 Hx0 Hn0; apply HK2;
      [exact Hx0 | unfold SegInstA.STK_reac_segconf_find in Hn0; lia | tauto]).
assert (KEEPm : fnd_kept (rdW W mem) (rdW W mem2) (spZ regs - FND_STK) (spZ regs))
  by (apply (fnd_kept_trans _ _ _ _ _ _ _ KEEPc KEEPk); lia).
clear HJ. rename HJ2 into HJ.
(* the cut, carried past the call *)
assert (CUT2 : forall regs3 mem3 md3,
  ajournal SEGS B FND_STK (spZ regs) [] ly S W mem md [] ly S W mem3 md3 0 ->
  fnd_kept (rdW W mem2) (rdW W mem3) (spZ regs - FND_STK) (spZ regs - 32) ->
  getr regs3 2 = w64 (spZ regs - 32) ->
  (getr regs3 3 = getr regs1 3 /\ getr regs3 4 = getr regs1 4 /\ getr regs3 19 = getr regs1 19 /\
   getr regs3 20 = getr regs1 20 /\ getr regs3 21 = getr regs1 21 /\ getr regs3 22 = getr regs1 22 /\
   getr regs3 23 = getr regs1 23 /\ getr regs3 24 = getr regs1 24 /\ getr regs3 25 = getr regs1 25 /\
   getr regs3 26 = getr regs1 26 /\ getr regs3 27 = getr regs1 27) ->
  fnd_cut B ly S W regs mem md regs3 mem3 md3).
{ intros regs3 mem3 md3 HJ3 HK3 R23 HKregs.
  apply (fnd_cut_kept B ly S W regs mem md ch c name HPRE Hc64 Hnm64 regs1 mem1 md1 regs3 mem3 md3
           (spZ regs - FND_STK) (spZ regs - 32));
    [split; [exact HJ0|]; split; [exact HK|]; split; [exact HFR|]; split; [exact R2 | exact RKall]
    | exact HJ3
    | apply (fnd_kept_trans _ _ _ _ _ _ _
               (fnd_kept_widen _ _ _ _ (spZ regs - FND_STK) (spZ regs - 32) KEEP1 ltac:(lia) ltac:(lia))
               (fnd_kept_trans _ _ _ _ _ _ _ KEEPk HK3 ltac:(lia) ltac:(lia))); lia
    | lia | lia
    | rewrite R23, R2; reflexivity
    | exact HKregs]. }
(* 0x89550: beqz a0, the wrapper's answer *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* strcmp = 0: entry k is the one; 0x89568 sets a0 := s0 and falls into the epilogue *)
  assert (HEQ : sx = seg_spec.zb nm).
  { apply HQ2. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq.
    cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite A52 in Hc. exact Hc. }
  assert (HM : (SegModel.strcmp (rs_name (r_seg rcs k)) nm =? 0) = true).
  { apply Z.eqb_eq. apply (seg_query_facts.sq_name_cmp sx (seg_spec.zb nm) _ nm HXZ HYZ HNN
      (proj2 (proj1 HNstr))). exact HEQ. }
  rewrite HM in RF.
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_EPI.
  { awr_ok_tac; exact Usp3. }
  fnd_md.
  fnd_keep_empty HFr KEEP4 (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
  apply (fnd_epi B ly S W regs mem md ch c name rcs nm HPRE Hc64 Hnm64 (c + 356 * Z.of_nat k)).
  + apply CUT2;
      [exact HJ | apply (fnd_kept_widen _ _ _ _ (spZ regs - FND_STK) (spZ regs - 32) KEEP4); lia | | ].
    * rewrite Q2. rewrite OLD3 by lia. unfold w64. rewrite <- Usp, Z_to_bv_bv_unsigned. reflexivity.
    * repeat split;
        (rewrite (st_ok_pi_restrict_reg (w_H W) Ec _ _ _ HS); cbn [ms_regs];
         lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
           let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
         cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?OLD3 by lia;
         first [ apply EE; reflexivity
               | rewrite (HP2 _ ltac:(unfold acallee_saved; lia)); apply EE; reflexivity ]).
  + rewrite Q10, OLD3 by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite E8. exact R8.
  + unfold seg_spec.find_ptr. rewrite RF. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. reflexivity.
- (* strcmp <> 0: the next entry, or none left *)
  assert (HNE : sx <> seg_spec.zb nm).
  { intros Heq. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc.
    unfold U. f_equal. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52.
    rewrite (proj2 HQ2 Heq). reflexivity. }
  assert (HM : (SegModel.strcmp (rs_name (r_seg rcs k)) nm =? 0) = false).
  { apply Z.eqb_neq. intros Hq. apply HNE.
    apply (seg_query_facts.sq_name_cmp sx (seg_spec.zb nm) _ nm HXZ HYZ HNN (proj2 (proj1 HNstr))). exact Hq. }
  rewrite HM in RF. clear Hc.
  (* 0x89554 .. 0x8955c: s2 := s2 - 1, s0 := s0 + 356, bnez s2 *)
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac; exact Usp3. }
  fnd_md.
  fnd_keep_empty HFr KEEP4 (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* entries left: back to the loop head with k + 1 *)
    assert (HkS : (Datatypes.S k < length (rc_seg rcs))%nat).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite OLD3 in Hc by lia. rewrite E18, R18 in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. unfold w64 in Hc.
      rewrite unsigned_lit_small in Hc by lia. rewrite !zcanon_small in Hc by lia. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_LH.
    { awr_ok_tac; exact Usp3. }
    fnd_md.
    fnd_keep_empty HFr KEEP5 (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
    prreg HS (18%bv : bv 5) Q18.
    apply (NXT HkS).
    split; [|split; [lia|]].
    * apply CUT2; [exact HJ
        | apply (fnd_kept_widen _ _ _ _ (spZ regs - FND_STK) (spZ regs - 32)
                   (fnd_kept_trans _ _ _ _ _ _ _ KEEP4 KEEP5 ltac:(lia) ltac:(lia))); lia | |].
      -- rewrite Q2. rewrite OLD3 by lia. unfold w64. rewrite <- Usp, Z_to_bv_bv_unsigned. reflexivity.
      -- repeat split;
           (rewrite (st_ok_pi_restrict_reg (w_H W) Ec _ _ _ HS); cbn [ms_regs];
            lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
              let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
            cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?OLD3 by lia;
            first [ apply EE; reflexivity
                  | rewrite (HP2 _ ltac:(unfold acallee_saved; lia)); apply EE; reflexivity ]).
    * split; [exact RF|].
      split; [rewrite Q8, OLD3, E8, R8 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
      split; [rewrite Q9, OLD3, E9 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R9|].
      rewrite Q18, OLD3, E18, R18 by lia. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  + (* no entry left: 0x89560 sets a0 := 0 and jumps to the epilogue *)
    assert (HkS : Datatypes.S k = length (rc_seg rcs)).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite OLD3 in Hc by lia. rewrite E18, R18 in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. unfold w64 in Hc.
      rewrite unsigned_lit_small in Hc by lia. rewrite !zcanon_small in Hc by lia. lia. }
    replace (Datatypes.S k) with (length (rc_seg rcs)) in RF by lia.
    rewrite seg_query_facts.sq_find_go_end in RF.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan FND_EPI.
    { awr_ok_tac; exact Usp3. }
    fnd_md.
    fnd_keep_empty HFr KEEP5 (spZ regs - FND_STK) (spZ regs - FND_STK). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
    apply (fnd_epi B ly S W regs mem md ch c name rcs nm HPRE Hc64 Hnm64 0).
    * apply CUT2; [exact HJ
        | apply (fnd_kept_widen _ _ _ _ (spZ regs - FND_STK) (spZ regs - 32)
                   (fnd_kept_trans _ _ _ _ _ _ _ KEEP4 KEEP5 ltac:(lia) ltac:(lia))); lia | |].
      -- rewrite Q2. rewrite OLD3 by lia. unfold w64. rewrite <- Usp, Z_to_bv_bv_unsigned. reflexivity.
      -- repeat split;
           (rewrite (st_ok_pi_restrict_reg (w_H W) Ec _ _ _ HS); cbn [ms_regs];
            lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
              let q := eval vm_compute in (sr_get a rr2) in replace (sr_get a rr2) with q by (vm_compute; reflexivity) end;
            cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?OLD3 by lia;
            first [ apply EE; reflexivity
                  | rewrite (HP2 _ ltac:(unfold acallee_saved; lia)); apply EE; reflexivity ]).
    * exact Q10.
    * unfold seg_spec.find_ptr. rewrite RF. reflexivity.
Qed.

(* ---------- the loop: induction on the entries left ---------- *)
Lemma fnd_loop : forall dd k regs1 mem1 md1, (k + Datatypes.S dd = length (rc_seg rcs))%nat ->
LHP k regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + FND_LH)) mem1 (seg_rom SEGS)) md1) QQ.
Proof using ART ASTRCMP HPRE HQP HROD Hc64 Hnm64.
induction dd as [|dd IH]; intros k regs1 mem1 md1 Hd HLH.
- apply (fnd_loop_step k regs1 mem1 md1); [intros Hk2; lia | exact HLH].
- apply (fnd_loop_step k regs1 mem1 md1); [|exact HLH].
  intros _ r m d HLH2. apply (IH (Datatypes.S k) r m d); [lia | exact HLH2].
Qed.

Lemma fnd_core : SRr SEGS W (cfg_at SEGS (BASE + AF_reac_segconf_find) regs mem md) QQ.
Proof using ART ASTRCMP H10 H11 HPRE HQP HROD Hc64 Hnm64.
apply (fnd_entry B TL ly S W regs mem md ch c name rcs nm HPRE H10 Hc64 H11 Hnm64 HQP).
intros k regs1 mem1 md1 HLH.
apply (fnd_loop (length (rc_seg rcs) - k - 1)%nat k regs1 mem1 md1);
  [destruct HLH as (_ & Hk & _); lia | exact HLH].
Qed.

End w.

Theorem reac_segconf_find_walk :
  reac_segconf_find_contract SEGS B (BASE + AF_reac_segconf_find) SegInstA.STK_reac_segconf_find
    SegInstA.RLO_A SegInstA.RHI_A.
Proof using ART ASTRCMP.
unfold reac_segconf_find_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Hc64 H11 Hnm64 HQP _.
exact (fnd_core ly S W regs mem md ch SegInstA.RLO_A SegInstA.RHI_A c name rcs nm HPRE HROD H10 Hc64 H11 Hnm64 HQP).
Qed.
End e.
End d.
End b.

(* evidence for the lane's answer: the walk rests only on the standard library axioms the released
   plugin-hostd/fuzz_command walks show, and keeps exactly the Section hypotheses the contract names. *)
Print Assumptions reac_segconf_find_walk.
About reac_segconf_find_walk.
